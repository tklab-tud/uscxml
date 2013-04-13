#include "uscxml/config.h"
#include "uscxml/Interpreter.h"
#include <glog/logging.h>

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

void printUsageAndExit() {
	printf("w3c-test version " USCXML_VERSION " (" CMAKE_BUILD_TYPE " build - " CMAKE_COMPILER_STRING ")\n");
	printf("Usage\n");
	printf("\tmmi-browser");
#ifdef BUILD_AS_PLUGINS
	printf(" [-p pluginPath]");
#endif
	printf(" URL\n");
	printf("\n");
	exit(1);
}

class W3CStatusMonitor : public uscxml::InterpreterMonitor {
	void beforeCompletion(uscxml::Interpreter interpreter) {
		Arabica::XPath::NodeSet<std::string> config = interpreter.getConfiguration();
		if (config.size() == 1 && boost::iequals(ATTR(config[0], "id"), "pass"))
			exit(EXIT_SUCCESS);
		exit(EXIT_FAILURE);
	}
};

int main(int argc, char** argv) {
	using namespace uscxml;

	std::set_terminate(customTerminate);

#if defined(HAS_SIGNAL_H) && !defined(WIN32)
	signal(SIGPIPE, SIG_IGN);
#endif

	if (argc < 2) {
		printUsageAndExit();
	}

	google::InitGoogleLogging(argv[0]);
	google::LogToStderr();

#ifndef _WIN32
	opterr = 0;
#endif
	int option;
	while ((option = getopt(argc, argv, "vl:p:")) != -1) {
		switch(option) {
		case 'l':
			google::InitGoogleLogging(optarg);
			break;
		case 'p':
			uscxml::Factory::pluginPath = optarg;
			break;
		case '?':
			break;
		default:
			printUsageAndExit();
			break;
		}
	}

//  for (int i = 0; i < argc; i++)
//    std::cout << argv[i] << std::endl;
//  std::cout << optind << std::endl;

	LOG(INFO) << "Processing " << argv[optind];
	Interpreter interpreter = Interpreter::fromURI(argv[optind]);
	if (interpreter) {
		interpreter.setCmdLineOptions(argc, argv);
//		interpreter->setCapabilities(Interpreter::CAN_NOTHING);
//		interpreter->setCapabilities(Interpreter::CAN_BASIC_HTTP | Interpreter::CAN_GENERIC_HTTP);

		W3CStatusMonitor* vm = new W3CStatusMonitor();
		interpreter.addMonitor(vm);

		interpreter.start();
		while(interpreter.runOnMainThread(25));
	}

	return EXIT_SUCCESS;
}