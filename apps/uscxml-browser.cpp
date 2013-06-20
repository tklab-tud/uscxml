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

class VerboseMonitor : public uscxml::InterpreterMonitor {
	void onStableConfiguration(uscxml::Interpreter interpreter) {
		printConfig(interpreter.getConfiguration());
	}

	void beforeCompletion(uscxml::Interpreter interpreter) {
		printConfig(interpreter.getConfiguration());
	}

	void printConfig(const Arabica::XPath::NodeSet<std::string>& config) {
		std::string seperator;
		std::cout << "Config: {";
		for (int i = 0; i < config.size(); i++) {
			std::cout << seperator << ATTR(config[i], "id");
			seperator = ", ";
		}
		std::cout << "}" << std::endl;
	}
};


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
	printf("uscxml-browser version " USCXML_VERSION " (" CMAKE_BUILD_TYPE " build - " CMAKE_COMPILER_STRING ")\n");
	printf("Usage\n");
	printf("\tuscxml-browser");
#ifdef BUILD_AS_PLUGINS
	printf(" [-d pluginPath]");
#endif
	printf(" URL\n");
	printf("\n");
	printf("Options\n");
	printf("\t-v        : be verbose\n");
	printf("\t-pN       : port for HTTP server\n");
	printf("\n");
	exit(1);
}

int main(int argc, char** argv) {
	using namespace uscxml;

	std::set_terminate(customTerminate);

#if defined(HAS_SIGNAL_H) && !defined(WIN32)
	signal(SIGPIPE, SIG_IGN);
#endif

	if (argc < 2) {
		printUsageAndExit();
	}

	bool verbose = false;
	size_t port = 8080;
	google::InitGoogleLogging(argv[0]);
	google::LogToStderr();

#ifndef _WIN32
	opterr = 0;
#endif
	int option;
	while ((option = getopt(argc, argv, "vl:d:p:")) != -1) {
		switch(option) {
		case 'l':
			google::InitGoogleLogging(optarg);
			break;
		case 'd':
			uscxml::Factory::pluginPath = optarg;
			break;
		case 'p':
			port = strTo<size_t>(optarg);
			break;
		case 'v':
			verbose = true;
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

	// intialize http server on given port
	HTTPServer::getInstance(port);

	LOG(INFO) << "Processing " << argv[optind];
	Interpreter interpreter = Interpreter::fromURI(argv[optind]);
	if (interpreter) {
		interpreter.setCmdLineOptions(argc, argv);
//		interpreter->setCapabilities(Interpreter::CAN_NOTHING);
//		interpreter->setCapabilities(Interpreter::CAN_BASIC_HTTP | Interpreter::CAN_GENERIC_HTTP);

		if (verbose) {
			VerboseMonitor* vm = new VerboseMonitor();
			interpreter.addMonitor(vm);
		}

		interpreter.start();
		while(interpreter.runOnMainThread(25));
	}

	return EXIT_SUCCESS;
}