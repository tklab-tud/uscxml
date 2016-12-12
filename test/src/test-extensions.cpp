#include "uscxml/Interpreter.h"
#include "uscxml/interpreter/InterpreterMonitor.h"
#include "uscxml/interpreter/InterpreterImpl.h"
#include "uscxml/interpreter/BasicEventQueue.h"
#include "uscxml/interpreter/BasicDelayedEventQueue.h"

#include <event2/util.h>                // for evutil_socket_t

#include <chrono>
#include <mutex>

using namespace uscxml;

// from issue 96:
// https://github.com/tklab-tud/uscxml/issues/96

static const char *customDelayedEQ =
    "<scxml initial=\"StateShape1\" name=\"ScxmlShape1\" version=\"1.0\" xmlns=\"http://www.w3.org/2005/07/scxml\">"
    "   <state id=\"StateShape1\">"
    "       <invoke autoforward=\"true\" type=\"scxml\">"
    "			<content>"
    "				<scxml initial=\"StateShape1\" name=\"Include\" version=\"1.0\" xmlns=\"http://www.w3.org/2005/07/scxml\">"
    "					<state id=\"StateShape1\">"
    "						<transition event=\"error.*\" target=\"FinalShape1\"/>"
    "						<state id=\"Step1\">"
    "							<onentry>"
    "								<send delay=\"1s\" event=\"Timer2\"/>"
    "								<log expr=\"'Hello from step1'\"/>"
    "							</onentry>"
    "							<transition event=\"Timer2\" target=\"Step2\"/>"
    "						</state>"
    "						<state id=\"Step2\">"
    "							<onentry>"
    "								<send delay=\"1s\" event=\"Timer2\"/>"
    "								<log expr=\"'Hello from step2'\"/>"
    "							</onentry>"
    "							<transition event=\"Timer2\" target=\"Step1\"/>"
    "						</state>"
    "					</state>"
    "					<final id=\"FinalShape1\"/>"
    "				</scxml>"
    "			</content>"
    "		</invoke>"
    "	</state>"
    "	<final id=\"FinalShape1\"/>"
    "</scxml>";

class PausableDelayedEventQueue;
std::shared_ptr<PausableDelayedEventQueue> nestedDelayQueue;

/**
 * A DelayedEventQueue that implements pause/resume
 */
class PausableDelayedEventQueue : public BasicDelayedEventQueue {
public:
	PausableDelayedEventQueue(DelayedEventQueueCallbacks* callbacks) : BasicDelayedEventQueue(callbacks) {
        _pausedAt.tv_sec = 0;
        _pausedAt.tv_usec = 0;
    }

	std::shared_ptr<DelayedEventQueueImpl> create(DelayedEventQueueCallbacks* callbacks) {
		// remember as nestedDelayQueue in global scope
		nestedDelayQueue = std::shared_ptr<PausableDelayedEventQueue>(new PausableDelayedEventQueue(callbacks));
		return nestedDelayQueue;
	}

	void pause() {
		if(_pausedAt.tv_sec != 0 || _pausedAt.tv_usec != 0) {
			return; // we are already paused!
		}

		evutil_gettimeofday(&_pausedAt, NULL); // remember when we paused

		{
			// Verbatim copy of stop() without cancelAllDelayed()
			if (_isStarted) {
				_isStarted = false;
				event_base_loopbreak(_eventLoop);
			}
			if (_thread) {
				_thread->join();
				delete _thread;
				_thread = NULL;
			}
		}

		std::lock_guard<std::recursive_mutex> lock(_mutex);

		// remove all events from libevent without deleting them
		for(auto callbackData : _callbackData) {
			Event data = callbackData.second.userData;
			event_del(callbackData.second.event);
		}
	}

	void resume() {
		if (_pausedAt.tv_sec != 0 || _pausedAt.tv_usec != 0) {
			struct timeval now;
			struct timeval pausedFor;

			evutil_gettimeofday(&now, NULL);
			evutil_timersub(&now, &_pausedAt, &pausedFor);
            _pausedAt.tv_sec = 0;
            _pausedAt.tv_usec = 0;

			for(auto& callbackData : _callbackData) {
				// add the time we were paused to all due times
				evutil_timeradd(&callbackData.second.due, &pausedFor, &callbackData.second.due);

				struct timeval remain;
				evutil_timersub(&callbackData.second.due, &now, &remain);

#if 0
				std::cout << "Now      : " << now.tv_sec << "." << now.tv_usec << std::endl;
				std::cout << "Paused   : " << pausedFor.tv_sec << "." << pausedFor.tv_usec << std::endl;
				std::cout << "Remaining: " << remain.tv_sec << "." << remain.tv_usec << std::endl;
#endif
				assert(remain.tv_usec >= 0 && remain.tv_sec >= 0);

				// reenqueue with libevent
				event_add(callbackData.second.event, &remain);
			}
		}
		start();
	}

protected:
	timeval _pausedAt;
};

bool testPausableEventQueue() {
	Interpreter interpreter = Interpreter::fromXML(customDelayedEQ, "");

	PausableDelayedEventQueue* queue = new PausableDelayedEventQueue(interpreter.getImpl().get());
	ActionLanguage lang;
	lang.delayedQueue = DelayedEventQueue(std::shared_ptr<DelayedEventQueueImpl>(queue));

	interpreter.setActionLanguage(lang);

	StateTransitionMonitor mon;
	mon.copyToInvokers(true);
	interpreter.addMonitor(&mon);

	size_t iterations = 10;

	InterpreterState state = InterpreterState::USCXML_UNDEF;
	while (state != USCXML_FINISHED) {
		state = interpreter.step();
		if (nestedDelayQueue) {
			/*
			 * As soon as we have the nested event queue instantiated, we pause and resume it
			 * We pause for 500ms, and run for 500ms. This will effectively double the time required
			 * for delayed events.
			 * This would usually done in another thread ..
			 */
			std::cout << "<- pausing" << std::endl;
			nestedDelayQueue->pause();
			std::this_thread::sleep_for(std::chrono::milliseconds(500));
			std::cout << "-> continuing" << std::endl;
			nestedDelayQueue->resume();
			std::this_thread::sleep_for(std::chrono::milliseconds(500));

			if (iterations-- == 0)
				return true;
		}
	}

	return true;

}

int main(int argc, char** argv) {
	testPausableEventQueue();
}
