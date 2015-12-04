#include "uscxml/config.h"
#include "uscxml/Interpreter.h"
#include <glog/logging.h>

#include "uscxml/plugins/invoker/filesystem/dirmon/DirMonInvoker.h"
#include <boost/algorithm/string.hpp>

#ifdef HAS_SIGNAL_H
#include <signal.h>
#endif

#ifdef HAS_EXECINFO_H
#include <execinfo.h>
#endif

#ifdef HAS_DLFCN_H
#include <dlfcn.h>
#endif

#ifdef _WIN32
#include "XGetopt.h"
#endif

int startedAt;
int lastTransitionAt;
bool testIssue56();

#ifdef HAS_EXECINFO_H
void printBacktrace(void** array, int size) {
	char** messages = backtrace_symbols(array, size);
	for (int i = 0; i < size && messages != NULL; ++i) {
		std::cerr << "\t" << messages[i] << std::endl;
	}
	std::cerr << std::endl;
	free(messages);
}

#ifdef HAS_DLFCN_H
// see https://gist.github.com/nkuln/2020860
typedef void (*cxa_throw_type)(void *, void *, void (*) (void *));
cxa_throw_type orig_cxa_throw = 0;

void load_orig_throw_code() {
	orig_cxa_throw = (cxa_throw_type) dlsym(RTLD_NEXT, "__cxa_throw");
}

extern "C"
CXA_THROW_SIGNATURE {
	std::cerr << __FUNCTION__ << " will throw exception from " << std::endl;
	if (orig_cxa_throw == 0)
		load_orig_throw_code();

	void *array[50];
	size_t size = backtrace(array, 50);
	printBacktrace(array, size);
	orig_cxa_throw(thrown_exception, pvtinfo, dest);
}
#endif
#endif


// see http://stackoverflow.com/questions/2443135/how-do-i-find-where-an-exception-was-thrown-in-c
void customTerminate() {
	static bool tried_throw = false;
	try {
		// try once to re-throw currently active exception
		if (!tried_throw) {
			throw;
			tried_throw = true;
		} else {
			tried_throw = false;
		};
	} catch (const std::exception &e) {
		std::cerr << __FUNCTION__ << " caught unhandled exception. what(): "
		          << e.what() << std::endl;
	} catch (const uscxml::Event &e) {
		std::cerr << __FUNCTION__ << " caught unhandled exception. Event: "
		          << e << std::endl;
	} catch (...) {
		std::cerr << __FUNCTION__ << " caught unknown/unhandled exception."
		          << std::endl;
	}

#ifdef HAS_EXECINFO_H
	void * array[50];
	int size = backtrace(array, 50);

	printBacktrace(array, size);
#endif
	abort();
}

using namespace uscxml;

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
	virtual void beforeProcessingEvent(Interpreter interpreter, const Event& event) {
		CHECK_CALLBACK_TYPE(USCXML_BEFOREPROCESSINGEVENT);
	}
	virtual void beforeMicroStep(Interpreter interpreter) {
		CHECK_CALLBACK_TYPE(USCXML_BEFOREMICROSTEP);
	}

	virtual void beforeExitingState(Interpreter interpreter, const Arabica::DOM::Element<std::string>& state, bool moreComing) {
		if (!moreComing)
			CHECK_CALLBACK_TYPE(USCXML_BEFOREEXITINGSTATE);
	}
	virtual void afterExitingState(Interpreter interpreter, const Arabica::DOM::Element<std::string>& state, bool moreComing) {
		if (!moreComing)
			CHECK_CALLBACK_TYPE(USCXML_AFTEREXITINGSTATE);
	}

	virtual void beforeExecutingContent(Interpreter interpreter, const Arabica::DOM::Element<std::string>& element) {
		CHECK_CALLBACK_TYPE(USCXML_BEFOREEXECUTINGCONTENT);
	}
	virtual void afterExecutingContent(Interpreter interpreter, const Arabica::DOM::Element<std::string>& element) {
		CHECK_CALLBACK_TYPE(USCXML_AFTEREXECUTINGCONTENT);
	}

	virtual void beforeUninvoking(Interpreter interpreter, const Arabica::DOM::Element<std::string>& invokeElem, const std::string& invokeid) {
		CHECK_CALLBACK_TYPE(USCXML_BEFOREUNINVOKING);
	}
	virtual void afterUninvoking(Interpreter interpreter, const Arabica::DOM::Element<std::string>& invokeElem, const std::string& invokeid) {
		CHECK_CALLBACK_TYPE(USCXML_AFTERUNINVOKING);
	}

	virtual void beforeTakingTransition(Interpreter interpreter, const Arabica::DOM::Element<std::string>& transition, bool moreComing) {
		if (!moreComing)
			CHECK_CALLBACK_TYPE(USCXML_BEFORETAKINGTRANSITION);
	}
	virtual void afterTakingTransition(Interpreter interpreter, const Arabica::DOM::Element<std::string>& transition, bool moreComing) {
		if (!moreComing)
			CHECK_CALLBACK_TYPE(USCXML_AFTERTAKINGTRANSITION);
	}

	virtual void beforeEnteringState(Interpreter interpreter, const Arabica::DOM::Element<std::string>& state, bool moreComing) {
		if (!moreComing)
			CHECK_CALLBACK_TYPE(USCXML_BEFOREENTERINGSTATE);
	}
	virtual void afterEnteringState(Interpreter interpreter, const Arabica::DOM::Element<std::string>& state, bool moreComing) {
		if (!moreComing)
			CHECK_CALLBACK_TYPE(USCXML_AFTERENTERINGSTATE);
	}

	virtual void beforeInvoking(Interpreter interpreter, const Arabica::DOM::Element<std::string>& invokeElem, const std::string& invokeid) {
		CHECK_CALLBACK_TYPE(USCXML_BEFOREINVOKING);
	}
	virtual void afterInvoking(Interpreter interpreter, const Arabica::DOM::Element<std::string>& invokeElem, const std::string& invokeid) {
		CHECK_CALLBACK_TYPE(USCXML_AFTERINVOKING);
	}

	virtual void afterMicroStep(Interpreter interpreter) {
		CHECK_CALLBACK_TYPE(USCXML_AFTERMICROSTEP);
	}

	virtual void onStableConfiguration(Interpreter interpreter) {
		CHECK_CALLBACK_TYPE(USCXML_ONSTABLECONFIGURATION);
	}

	virtual void beforeCompletion(Interpreter interpreter) {
		CHECK_CALLBACK_TYPE(USCXML_BEFORECOMPLETION);
	}
	virtual void afterCompletion(Interpreter interpreter) {
		CHECK_CALLBACK_TYPE(USCXML_AFTERCOMPLETION);
	}

};


int main(int argc, char** argv) {

	std::set_terminate(customTerminate);

#if defined(HAS_SIGNAL_H) && !defined(WIN32)
	signal(SIGPIPE, SIG_IGN);
#endif

	google::InitGoogleLogging(argv[0]);
	google::LogToStderr();

	SequenceCheckingMonitor* mon = new SequenceCheckingMonitor();

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
				interpreter.addMonitor(mon);
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
				interpreter.addMonitor(mon);
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
			interpreter.addMonitor(mon);

			callBackSeq.push_back(USCXML_BEFOREENTERINGSTATE);
			callBackSeq.push_back(USCXML_AFTERENTERINGSTATE);

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
			assert(interpreter.step() == USCXML_MICROSTEPPED);
			assert(interpreter.step() == USCXML_MICROSTEPPED);
			assert(interpreter.step() == USCXML_FINISHED);
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
			interpreter.addMonitor(mon);

			callBackSeq.push_back(USCXML_BEFOREENTERINGSTATE);
			callBackSeq.push_back(USCXML_AFTERENTERINGSTATE);

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
			assert(interpreter.step() == USCXML_MICROSTEPPED);
			assert(interpreter.step() == USCXML_FINISHED);
			interpreter.reset();

			callBackSeq.push_back(USCXML_BEFOREENTERINGSTATE);
			callBackSeq.push_back(USCXML_AFTERENTERINGSTATE);

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
			interpreter.addMonitor(mon);

			callBackSeq.push_back(USCXML_BEFOREENTERINGSTATE);
			callBackSeq.push_back(USCXML_BEFOREEXECUTINGCONTENT);
			callBackSeq.push_back(USCXML_AFTEREXECUTINGCONTENT);
			callBackSeq.push_back(USCXML_AFTERENTERINGSTATE);
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
			assert(interpreter.step() == USCXML_IDLE);
			assert(interpreter.step(true) == USCXML_MACROSTEPPED);
			assert(interpreter.step() == USCXML_MICROSTEPPED);
			assert(interpreter.step() == USCXML_FINISHED);
		}
	}
	return EXIT_SUCCESS;
}

