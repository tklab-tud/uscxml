#include "uscxml/config.h"
#include "uscxml/Interpreter.h"
#include "uscxml/interpreter/InterpreterMonitor.h"
#include "uscxml/interpreter/Logging.h"

#include <boost/algorithm/string.hpp>
#include <xercesc/util/PlatformUtils.hpp>

#ifdef _WIN32
#include "XGetopt.h"
#endif

int startedAt;
int lastTransitionAt;

using namespace uscxml;
using namespace XERCESC_NS;

enum CallbackType {
	USCXML_BEFOREPROCESSINGEVENT,
	USCXML_BEFOREMICROSTEP,
	USCXML_BEFOREEXITINGSTATE,
	USCXML_AFTEREXITINGSTATE,
	USCXML_BEFOREEXECUTINGCONTENT,
	USCXML_AFTEREXECUTINGCONTENT,
	USCXML_BEFOREUNINVOKING,
	USCXML_AFTERUNINVOKING,
	USCXML_BEFORETAKINGTRANSITION,
	USCXML_AFTERTAKINGTRANSITION,
	USCXML_BEFOREENTERINGSTATE,
	USCXML_AFTERENTERINGSTATE,
	USCXML_BEFOREINVOKING,
	USCXML_AFTERINVOKING,
	USCXML_AFTERMICROSTEP,
	USCXML_ONSTABLECONFIGURATION,
	USCXML_BEFORECOMPLETION,
	USCXML_AFTERCOMPLETION
};

std::list<CallbackType> callBackSeq;

#define CHECK_CALLBACK_TYPE(type)\
{\
	assert(!callBackSeq.empty());\
	assert(callBackSeq.front() == type);\
	callBackSeq.pop_front();\
}


class SequenceCheckingMonitor : public InterpreterMonitor {
	virtual void beforeProcessingEvent(Interpreter& interpreter, const Event& event) {
		CHECK_CALLBACK_TYPE(USCXML_BEFOREPROCESSINGEVENT);
	}
	virtual void beforeMicroStep(Interpreter& interpreter) {
		CHECK_CALLBACK_TYPE(USCXML_BEFOREMICROSTEP);
	}

	virtual void beforeExitingState(Interpreter& interpreter, const XERCESC_NS::DOMElement* state) {
		CHECK_CALLBACK_TYPE(USCXML_BEFOREEXITINGSTATE);
	}
	virtual void afterExitingState(Interpreter& interpreter, const XERCESC_NS::DOMElement* state) {
		CHECK_CALLBACK_TYPE(USCXML_AFTEREXITINGSTATE);
	}

	virtual void beforeExecutingContent(Interpreter& interpreter, const XERCESC_NS::DOMElement* element) {
		CHECK_CALLBACK_TYPE(USCXML_BEFOREEXECUTINGCONTENT);
	}
	virtual void afterExecutingContent(Interpreter& interpreter, const XERCESC_NS::DOMElement* element) {
		CHECK_CALLBACK_TYPE(USCXML_AFTEREXECUTINGCONTENT);
	}

	virtual void beforeUninvoking(Interpreter& interpreter, const XERCESC_NS::DOMElement* invokeElem, const std::string& invokeid) {
		CHECK_CALLBACK_TYPE(USCXML_BEFOREUNINVOKING);
	}
	virtual void afterUninvoking(Interpreter& interpreter, const XERCESC_NS::DOMElement* invokeElem, const std::string& invokeid) {
		CHECK_CALLBACK_TYPE(USCXML_AFTERUNINVOKING);
	}

	virtual void beforeTakingTransition(Interpreter& interpreter, const XERCESC_NS::DOMElement* transition) {
		CHECK_CALLBACK_TYPE(USCXML_BEFORETAKINGTRANSITION);
	}
	virtual void afterTakingTransition(Interpreter& interpreter, const XERCESC_NS::DOMElement* transition) {
		CHECK_CALLBACK_TYPE(USCXML_AFTERTAKINGTRANSITION);
	}

	virtual void beforeEnteringState(Interpreter& interpreter, const XERCESC_NS::DOMElement* state) {
		CHECK_CALLBACK_TYPE(USCXML_BEFOREENTERINGSTATE);
	}
	virtual void afterEnteringState(Interpreter& interpreter, const XERCESC_NS::DOMElement* state) {
		CHECK_CALLBACK_TYPE(USCXML_AFTERENTERINGSTATE);
	}

	virtual void beforeInvoking(Interpreter& interpreter, const XERCESC_NS::DOMElement* invokeElem, const std::string& invokeid) {
		CHECK_CALLBACK_TYPE(USCXML_BEFOREINVOKING);
	}
	virtual void afterInvoking(Interpreter& interpreter, const XERCESC_NS::DOMElement* invokeElem, const std::string& invokeid) {
		CHECK_CALLBACK_TYPE(USCXML_AFTERINVOKING);
	}

	virtual void afterMicroStep(Interpreter& interpreter) {
		CHECK_CALLBACK_TYPE(USCXML_AFTERMICROSTEP);
	}

	virtual void onStableConfiguration(Interpreter& interpreter) {
		CHECK_CALLBACK_TYPE(USCXML_ONSTABLECONFIGURATION);
	}

	virtual void beforeCompletion(Interpreter& interpreter) {
		CHECK_CALLBACK_TYPE(USCXML_BEFORECOMPLETION);
	}
	virtual void afterCompletion(Interpreter& interpreter) {
		CHECK_CALLBACK_TYPE(USCXML_AFTERCOMPLETION);
	}

};


int main(int argc, char** argv) {

	SequenceCheckingMonitor mon;

	int iterations = 1;

	while(iterations--) {

		if (1) {
			// syntactic xml parse error
			try {
				const char* xml = "<invalid";
				Interpreter interpreter = Interpreter::fromXML(xml, "");
				assert(false);
			} catch (Event& e) {
				std::cout << e;
			}
		}

		if (1) {
			// semantic xml parse error
			try {
				const char* xml = "<invalid />";
				Interpreter interpreter = Interpreter::fromXML(xml, "");
				interpreter.addMonitor(&mon);
				assert(interpreter.getState() == USCXML_INSTANTIATED);
				interpreter.step();
				assert(false);
			} catch (Event& e) {
				std::cout << e;
			}
		}

		if (1) {
			// request unknown datamodel
			try {
				const char* xml =
				    "<scxml datamodel=\"invalid\">"
				    "	<state id=\"start\">"
				    "		<transition target=\"done\" />"
				    " </state>"
				    " <final id=\"done\" />"
				    "</scxml>";
				Interpreter interpreter = Interpreter::fromXML(xml, "");
				interpreter.addMonitor(&mon);
				assert(interpreter.getState() == USCXML_INSTANTIATED);
				interpreter.step();
				assert(false);
			} catch (Event& e) {
				std::cout << e;
			}
		}

		if (1) {
			// two microsteps
			const char* xml =
			    "<scxml>"
			    "	<state id=\"start\">"
			    "		<transition target=\"s2\" />"
			    " </state>"
			    "	<state id=\"s2\">"
			    "		<transition target=\"done\" />"
			    " </state>"
			    " <final id=\"done\" />"
			    "</scxml>";

			Interpreter interpreter = Interpreter::fromXML(xml, "");
			interpreter.addMonitor(&mon);

			callBackSeq.push_back(USCXML_BEFOREMICROSTEP);
			callBackSeq.push_back(USCXML_BEFOREENTERINGSTATE); // scxml
			callBackSeq.push_back(USCXML_AFTERENTERINGSTATE);
			callBackSeq.push_back(USCXML_BEFOREENTERINGSTATE); // start
			callBackSeq.push_back(USCXML_AFTERENTERINGSTATE);
			callBackSeq.push_back(USCXML_AFTERMICROSTEP);

			callBackSeq.push_back(USCXML_BEFOREMICROSTEP);
			callBackSeq.push_back(USCXML_BEFOREEXITINGSTATE); // start
			callBackSeq.push_back(USCXML_AFTEREXITINGSTATE);
			callBackSeq.push_back(USCXML_BEFORETAKINGTRANSITION);
			callBackSeq.push_back(USCXML_AFTERTAKINGTRANSITION);
			callBackSeq.push_back(USCXML_BEFOREENTERINGSTATE); // s2
			callBackSeq.push_back(USCXML_AFTERENTERINGSTATE);
			callBackSeq.push_back(USCXML_AFTERMICROSTEP);

			callBackSeq.push_back(USCXML_BEFOREMICROSTEP);
			callBackSeq.push_back(USCXML_BEFOREEXITINGSTATE); // s2
			callBackSeq.push_back(USCXML_AFTEREXITINGSTATE);
			callBackSeq.push_back(USCXML_BEFORETAKINGTRANSITION);
			callBackSeq.push_back(USCXML_AFTERTAKINGTRANSITION);
			callBackSeq.push_back(USCXML_BEFOREENTERINGSTATE); // final
			callBackSeq.push_back(USCXML_AFTERENTERINGSTATE);
			callBackSeq.push_back(USCXML_AFTERMICROSTEP);

			callBackSeq.push_back(USCXML_BEFORECOMPLETION); // interpreter is finalizing
			callBackSeq.push_back(USCXML_AFTERCOMPLETION);

			assert(interpreter.getState() == USCXML_INSTANTIATED);
			assert(interpreter.step() == USCXML_INITIALIZED);
			assert(interpreter.step() == USCXML_MICROSTEPPED); // initial config
			assert(interpreter.step() == USCXML_MICROSTEPPED); // s2
			assert(interpreter.step() == USCXML_MICROSTEPPED); // done
			assert(interpreter.step() == USCXML_FINISHED); // cleaned up
			assert(callBackSeq.empty());
		}

		if (1) {
			// single macrostep, multiple runs
			const char* xml =
			    "<scxml>"
			    "	<state id=\"start\">"
			    "		<transition target=\"done\" />"
			    " </state>"
			    " <final id=\"done\" />"
			    "</scxml>";

			Interpreter interpreter = Interpreter::fromXML(xml, "");
			interpreter.addMonitor(&mon);

			callBackSeq.push_back(USCXML_BEFOREMICROSTEP);
			callBackSeq.push_back(USCXML_BEFOREENTERINGSTATE); // scxml
			callBackSeq.push_back(USCXML_AFTERENTERINGSTATE);
			callBackSeq.push_back(USCXML_BEFOREENTERINGSTATE); // start
			callBackSeq.push_back(USCXML_AFTERENTERINGSTATE);
			callBackSeq.push_back(USCXML_AFTERMICROSTEP);

			callBackSeq.push_back(USCXML_BEFOREMICROSTEP);
			callBackSeq.push_back(USCXML_BEFOREEXITINGSTATE); // start
			callBackSeq.push_back(USCXML_AFTEREXITINGSTATE);
			callBackSeq.push_back(USCXML_BEFORETAKINGTRANSITION);
			callBackSeq.push_back(USCXML_AFTERTAKINGTRANSITION);
			callBackSeq.push_back(USCXML_BEFOREENTERINGSTATE); // done
			callBackSeq.push_back(USCXML_AFTERENTERINGSTATE);
			callBackSeq.push_back(USCXML_AFTERMICROSTEP);

			callBackSeq.push_back(USCXML_BEFORECOMPLETION);
			callBackSeq.push_back(USCXML_AFTERCOMPLETION);

			assert(interpreter.getState() == USCXML_INSTANTIATED);
			assert(interpreter.step() == USCXML_INITIALIZED);
			assert(interpreter.step() == USCXML_MICROSTEPPED);
			assert(interpreter.step() == USCXML_MICROSTEPPED);
			assert(interpreter.step() == USCXML_FINISHED);
			assert(callBackSeq.empty());
			interpreter.reset();

			callBackSeq.push_back(USCXML_BEFOREMICROSTEP);
			callBackSeq.push_back(USCXML_BEFOREENTERINGSTATE); // scxml
			callBackSeq.push_back(USCXML_AFTERENTERINGSTATE);
			callBackSeq.push_back(USCXML_BEFOREENTERINGSTATE); // start
			callBackSeq.push_back(USCXML_AFTERENTERINGSTATE);
			callBackSeq.push_back(USCXML_AFTERMICROSTEP);

			callBackSeq.push_back(USCXML_BEFOREMICROSTEP);
			callBackSeq.push_back(USCXML_BEFOREEXITINGSTATE); // start
			callBackSeq.push_back(USCXML_AFTEREXITINGSTATE);
			callBackSeq.push_back(USCXML_BEFORETAKINGTRANSITION);
			callBackSeq.push_back(USCXML_AFTERTAKINGTRANSITION);
			callBackSeq.push_back(USCXML_BEFOREENTERINGSTATE); // done
			callBackSeq.push_back(USCXML_AFTERENTERINGSTATE);
			callBackSeq.push_back(USCXML_AFTERMICROSTEP);

			callBackSeq.push_back(USCXML_BEFORECOMPLETION);
			callBackSeq.push_back(USCXML_AFTERCOMPLETION);

			assert(interpreter.getState() == USCXML_INSTANTIATED);
			assert(interpreter.step() == USCXML_INITIALIZED);
			assert(interpreter.step() == USCXML_MICROSTEPPED);
			assert(interpreter.step() == USCXML_MICROSTEPPED);
			assert(interpreter.step() == USCXML_FINISHED);
		}

		if (1) {
			// macrostep in between
			const char* xml =
			    "<scxml>"
			    "	<state id=\"start\">"
			    "		<onentry>"
			    "			<send event=\"continue\" delay=\"2s\"/>"
			    "		</onentry>"
			    "		<transition target=\"s2\" event=\"continue\" />"
			    " </state>"
			    "	<state id=\"s2\">"
			    "		<transition target=\"done\" />"
			    " </state>"
			    " <final id=\"done\" />"
			    "</scxml>";

			Interpreter interpreter = Interpreter::fromXML(xml, "");
			interpreter.addMonitor(&mon);
			callBackSeq.push_back(USCXML_BEFOREMICROSTEP);
			callBackSeq.push_back(USCXML_BEFOREENTERINGSTATE); // scxml
			callBackSeq.push_back(USCXML_AFTERENTERINGSTATE);
			callBackSeq.push_back(USCXML_BEFOREENTERINGSTATE); // start
			callBackSeq.push_back(USCXML_BEFOREEXECUTINGCONTENT); // send
			callBackSeq.push_back(USCXML_AFTEREXECUTINGCONTENT);
			callBackSeq.push_back(USCXML_AFTERENTERINGSTATE);
			callBackSeq.push_back(USCXML_AFTERMICROSTEP);

			callBackSeq.push_back(USCXML_ONSTABLECONFIGURATION);
			callBackSeq.push_back(USCXML_BEFOREPROCESSINGEVENT);

			callBackSeq.push_back(USCXML_BEFOREMICROSTEP);
			callBackSeq.push_back(USCXML_BEFOREEXITINGSTATE);
			callBackSeq.push_back(USCXML_AFTEREXITINGSTATE);
			callBackSeq.push_back(USCXML_BEFORETAKINGTRANSITION);
			callBackSeq.push_back(USCXML_AFTERTAKINGTRANSITION);
			callBackSeq.push_back(USCXML_BEFOREENTERINGSTATE);
			callBackSeq.push_back(USCXML_AFTERENTERINGSTATE);
			callBackSeq.push_back(USCXML_AFTERMICROSTEP);

			callBackSeq.push_back(USCXML_BEFOREMICROSTEP);
			callBackSeq.push_back(USCXML_BEFOREEXITINGSTATE);
			callBackSeq.push_back(USCXML_AFTEREXITINGSTATE);
			callBackSeq.push_back(USCXML_BEFORETAKINGTRANSITION);
			callBackSeq.push_back(USCXML_AFTERTAKINGTRANSITION);
			callBackSeq.push_back(USCXML_BEFOREENTERINGSTATE);
			callBackSeq.push_back(USCXML_AFTERENTERINGSTATE);
			callBackSeq.push_back(USCXML_AFTERMICROSTEP);

			callBackSeq.push_back(USCXML_BEFORECOMPLETION);
			callBackSeq.push_back(USCXML_AFTERCOMPLETION);

			assert(interpreter.getState() == USCXML_INSTANTIATED);
			assert(interpreter.step() == USCXML_INITIALIZED);
			assert(interpreter.step() == USCXML_MICROSTEPPED);
			assert(interpreter.step() == USCXML_MACROSTEPPED);
			assert(interpreter.step(0) == USCXML_IDLE);
			assert(interpreter.step() == USCXML_MICROSTEPPED);
			assert(interpreter.step() == USCXML_MICROSTEPPED);
			assert(interpreter.step() == USCXML_FINISHED);
		}
	}
	return EXIT_SUCCESS;
}

