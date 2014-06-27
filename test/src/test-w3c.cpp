#include "uscxml/config.h"
#include "uscxml/Interpreter.h"
#include "uscxml/DOMUtils.h"

#include "uscxml/Factory.h"
#include "uscxml/server/HTTPServer.h"

#include "uscxml/transform/ChartToFSM.h"
#include <glog/logging.h>
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

static bool withFlattening = false;
static std::string documentURI;

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
void __cxa_throw (void *thrown_exception, void *pvtinfo, void (*dest)(void *)) {
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

class W3CStatusMonitor : public uscxml::InterpreterMonitor {

	void beforeTakingTransition(uscxml::Interpreter interpreter, const Arabica::DOM::Element<std::string>& transition, bool moreComing) {
		std::cout << "Transition: " << uscxml::DOMUtils::xPathForNode(transition) << std::endl;
	}

	void onStableConfiguration(uscxml::Interpreter interpreter) {
		std::cout << "Config: {";
		printNodeSet(interpreter.getConfiguration());
		std::cout << "}" << std::endl;
	}

	void beforeProcessingEvent(uscxml::Interpreter interpreter, const uscxml::Event& event) {
		std::cout << "Event: " << event.name << std::endl;
	}

	void beforeExitingState(uscxml::Interpreter interpreter, const Arabica::DOM::Element<std::string>& state, bool moreComing) {
		exitingStates.push_back(state);
		if (!moreComing) {
			std::cout << "Exiting: {";
			printNodeSet(exitingStates);
			std::cout << "}" << std::endl;
			exitingStates = Arabica::XPath::NodeSet<std::string>();
		}
	}

	void beforeEnteringState(uscxml::Interpreter interpreter, const Arabica::DOM::Element<std::string>& state, bool moreComing) {
		enteringStates.push_back(state);
		if (!moreComing) {
			std::cout << "Entering: {";
			printNodeSet(enteringStates);
			std::cout << "}" << std::endl;
			enteringStates = Arabica::XPath::NodeSet<std::string>();
		}

	}

	void printNodeSet(const Arabica::XPath::NodeSet<std::string>& config) {
		std::string seperator;
		for (int i = 0; i < config.size(); i++) {
			std::cout << seperator << ATTR(config[i], "id");
			seperator = ", ";
		}
	}

	void beforeCompletion(uscxml::Interpreter interpreter) {
		Arabica::XPath::NodeSet<std::string> config = interpreter.getConfiguration();
		if (config.size() == 1) {
			if (withFlattening) {
				std::cout << ATTR(config[0], "id") << std::endl;
				if (boost::starts_with(ATTR(config[0], "id"), "active-pass")) {
					std::cout << "TEST SUCCEEDED" << std::endl;
					exit(EXIT_SUCCESS);
				}
			} else {
				if (boost::iequals(ATTR(config[0], "id"), "pass")) {
					std::cout << "TEST SUCCEEDED" << std::endl;
					exit(EXIT_SUCCESS);
				}
			}
		}
		std::cout << "TEST FAILED" << std::endl;
		exit(EXIT_FAILURE);
	}

	Arabica::XPath::NodeSet<std::string> exitingStates;
	Arabica::XPath::NodeSet<std::string> enteringStates;
};

int main(int argc, char** argv) {
	using namespace uscxml;

	std::set_terminate(customTerminate);

#if defined(HAS_SIGNAL_H) && !defined(WIN32)
	signal(SIGPIPE, SIG_IGN);
#endif

	if (argc < 2) {
		exit(EXIT_FAILURE);
	}

	HTTPServer::getInstance(32954, 32955, NULL); // bind to some random tcp sockets for ioprocessor tests

	google::InitGoogleLogging(argv[0]);
	google::LogToStderr();


	for (int i = 1; i < argc; i++) {
		if (std::string(argv[i]) == "-f") {
			withFlattening = true;
		} else {
			documentURI = argv[i];
		}
	}

	Interpreter interpreter;
	LOG(INFO) << "Processing " << documentURI << (withFlattening ? " FSM converted" : "");
	if (withFlattening) {
		Interpreter flatInterpreter = Interpreter::fromURI(documentURI);
		interpreter = Interpreter::fromDOM(ChartToFSM::flatten(flatInterpreter).getDocument(), flatInterpreter.getNameSpaceInfo());
		interpreter.setNameSpaceInfo(interpreter.getNameSpaceInfo());
	} else {
		interpreter = Interpreter::fromURI(documentURI);
	}

	if (interpreter) {
//		interpreter.setCmdLineOptions(argc, argv);
//		interpreter->setCapabilities(Interpreter::CAN_NOTHING);
//		interpreter->setCapabilities(Interpreter::CAN_BASIC_HTTP | Interpreter::CAN_GENERIC_HTTP);

		W3CStatusMonitor* vm = new W3CStatusMonitor();
		interpreter.addMonitor(vm);

//		if (interpreter.getDataModel().getNames().find("ecmascript") != interpreter.getDataModel().getNames().end()) {
//		}

		interpreter.start();
		while(interpreter.runOnMainThread(25));
	}

	return EXIT_SUCCESS;
}