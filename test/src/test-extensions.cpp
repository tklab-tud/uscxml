#include "uscxml/Interpreter.h"
#include "uscxml/interpreter/InterpreterMonitor.h"
#include "uscxml/interpreter/InterpreterImpl.h"
#include "uscxml/interpreter/BasicEventQueue.h"
#include "uscxml/interpreter/BasicDelayedEventQueue.h"
#include "uscxml/PausableDelayedEventQueue.h"
#include "uscxml/ExtendedLuaDataModel.h"
#include "uscxml/CustomExecutableContent.h"

#include <event2/util.h>                // for evutil_socket_t

#include <chrono>
#include <mutex>
#include <iostream>

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
	lang.delayQueue = DelayedEventQueue(std::shared_ptr<DelayedEventQueueImpl>(queue));

	interpreter.setActionLanguage(lang);

	StateTransitionMonitor mon;
	mon.copyToInvokers(true);
	interpreter.addMonitor(&mon);

	size_t iterations = 10;
	int now = time(NULL);
	int startedAt = time(NULL);

	InterpreterState state = InterpreterState::USCXML_UNDEF;
	while (state != USCXML_FINISHED && now - startedAt < 5) {
		state = interpreter.step(200);
		now = time(NULL);

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

static const char *customLuaExtension =
    "<scxml datamodel=\"lua\">"
    "  <script>"
    "    GetSomeResult();"
    "  </script>"
    "  <state/>"
    "</scxml>"
    ;

bool testLuaExtension() {
	Factory::getInstance()->registerDataModel(new ExtendedLuaDataModel());
	Interpreter exLua = Interpreter::fromXML(customLuaExtension, "");
	InterpreterState state;

	while ((state = exLua.step(0)) != USCXML_IDLE) {}

	return true;
}

static const char *customExecContent =
    "<scxml>"
    "  <state>"
    "    <onentry>"
    "      <custom />"
    "    </onentry>"
    "  </state>"
    "</scxml>"
    ;

bool testCustomExecContent() {
	Factory::getInstance()->registerExecutableContent(new CustomExecutableContent());
	Interpreter exContent = Interpreter::fromXML(customExecContent, "");
	InterpreterState state;

	while ((state = exContent.step(0)) != USCXML_IDLE) {}

	return true;
}

class CustomExecutableContentNS : public ExecutableContentImpl {
public:
	~CustomExecutableContentNS() {};
	virtual std::shared_ptr<ExecutableContentImpl> create(uscxml::InterpreterImpl* interpreter) {
		return std::shared_ptr<ExecutableContentImpl>(new CustomExecutableContentNS());
	}
	virtual std::string getLocalName() {
		return "custom";
	}
	virtual std::string getNamespace() {
		return "http://www.example.com/custom";
	}

	virtual void enterElement(XERCESC_NS::DOMElement* node) {
		std::cout << "Entering customNS element" << std::endl;
	}
	virtual void exitElement(XERCESC_NS::DOMElement* node) {
		std::cout << "Exiting customNS element" << std::endl;
	}
};

static const char *customExecContentNS =
    "<scxml xmlns:custom=\"http://www.example.com/custom\">"
    "  <state>"
    "    <onentry>"
    "      <custom:custom />"
    "    </onentry>"
    "  </state>"
    "</scxml>"
    ;

bool testCustomExecContentNS() {
	Factory::getInstance()->registerExecutableContent(new CustomExecutableContentNS());
	Interpreter exContent = Interpreter::fromXML(customExecContentNS, "");
	InterpreterState state;

	while ((state = exContent.step(0)) != USCXML_IDLE) {}

	return true;
}

int main(int argc, char** argv) {
//	testLuaExtension();
//	testPausableEventQueue();
	testCustomExecContentNS();
}
