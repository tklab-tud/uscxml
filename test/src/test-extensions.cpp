#include "uscxml/Interpreter.h"
#include "uscxml/interpreter/InterpreterMonitor.h"
#include "uscxml/interpreter/InterpreterImpl.h"
#include "uscxml/interpreter/BasicEventQueue.h"
#include "uscxml/interpreter/BasicDelayedEventQueue.h"
#include "uscxml/PausableDelayedEventQueue.h"

#include <event2/util.h>                // for evutil_socket_t

#include <chrono>
#include <mutex>

using namespace uscxml;
class MyPausableDelayedEventQueue;

std::shared_ptr<MyPausableDelayedEventQueue> nestedDelayQueue;

class MyPausableDelayedEventQueue : public PausableDelayedEventQueue {
	MyPausableDelayedEventQueue(DelayedEventQueueCallbacks* callbacks) : PausableDelayedEventQueue(callbacks) {
	}

	std::shared_ptr<DelayedEventQueueImpl> create(DelayedEventQueueCallbacks* callbacks) {
		// remember as nestedDelayQueue in global scope
		nestedDelayQueue = std::shared_ptr<MyPausableDelayedEventQueue>(new MyPausableDelayedEventQueue(callbacks));
		return nestedDelayQueue;
	}
};


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
