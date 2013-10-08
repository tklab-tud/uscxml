#include "uscxml/config.h"
#include "uscxml/Interpreter.h"
#include "uscxml/debug/SCXMLDotWriter.h"
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

#ifdef CMAKE_BUILD_TYPE_DEBUG

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
			tried_throw = true;
			throw;
		} else {
			tried_throw = false;
		}
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
#endif

int main(int argc, char** argv) {
	using namespace uscxml;

#if defined(HAS_SIGNAL_H) && !defined(WIN32)
	signal(SIGPIPE, SIG_IGN);
#endif

#ifdef CMAKE_BUILD_TYPE_DEBUG
	std::set_terminate(customTerminate);
#endif

	InterpreterOptions options = InterpreterOptions::fromCmdLine(argc, argv);
	if (!options) {
		InterpreterOptions::printUsageAndExit(argv[0]);
	}
	
	// setup logging
	google::LogToStderr();
	google::InitGoogleLogging(argv[0]);

	// setup HTTP server
	HTTPServer::SSLConfig* sslConf = NULL;
	if (options.certificate.length() > 0) {
		sslConf = new HTTPServer::SSLConfig();
		sslConf->privateKey = options.certificate;
		sslConf->publicKey = options.certificate;
		sslConf->port = options.httpsPort;
		
	} else if (options.privateKey.length() > 0 && options.publicKey.length() > 0) {
		sslConf = new HTTPServer::SSLConfig();
		sslConf->privateKey = options.privateKey;
		sslConf->publicKey = options.publicKey;
		sslConf->port = options.httpsPort;
		
	}
	HTTPServer::getInstance(options.httpPort, sslConf);

	// instantiate and configure interpreters
	std::list<Interpreter> interpreters;
	std::map<std::string, InterpreterOptions*>::iterator confIter = options.interpreters.begin();
	while(confIter != options.interpreters.end()) {

		InterpreterOptions* currOptions = confIter->second;
		std::string documentURL = confIter->first;
		
		LOG(INFO) << "Processing " << documentURL;
		Interpreter interpreter = Interpreter::fromURI(documentURL);
		if (interpreter) {
			interpreter.setCmdLineOptions(currOptions->additionalParameters);
			interpreter.setCapabilities(options.getCapabilities());

			if (options.verbose) {
				VerboseMonitor* vm = new VerboseMonitor();
				interpreter.addMonitor(vm);
			}
			if (options.useDot) {
				SCXMLDotWriter* dotWriter = new SCXMLDotWriter();
				interpreter.addMonitor(dotWriter);
			}
			
			interpreters.push_back(interpreter);

		} else {
			LOG(ERROR) << "Cannot create interpreter from " << documentURL;
		}
		confIter++;
	}

	// start interpreters
	std::list<Interpreter>::iterator interpreterIter = interpreters.begin();
	while(interpreterIter != interpreters.end()) {
		interpreterIter->start();
		interpreterIter++;
	}

	// call from main thread for UI events
	while(interpreters.size() > 0) {
		interpreterIter = interpreters.begin();
		while(interpreterIter != interpreters.end()) {
			interpreterIter->runOnMainThread(25);
			interpreterIter++;
		}
	}
	
	return EXIT_SUCCESS;
}