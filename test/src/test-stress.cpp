#include "uscxml/config.h"
#include "uscxml/Interpreter.h"
#include "uscxml/Factory.h"
#include "uscxml/server/HTTPServer.h"

#include <glog/logging.h>

#include "uscxml/plugins/invoker/filesystem/dirmon/DirMonInvoker.h"
#include <boost/algorithm/string.hpp>

#ifdef _WIN32
#include "XGetopt.h"
#endif

int startedAt;
int lastTransitionAt;

#ifdef HAS_SIGNAL_H
#include <signal.h>
#endif

#ifdef HAS_EXECINFO_H
#include <execinfo.h>
#endif

#ifdef HAS_DLFCN_H
#include <dlfcn.h>
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

void printUsageAndExit() {
	printf("test-stress version " USCXML_VERSION " (" CMAKE_BUILD_TYPE " build - " CMAKE_COMPILER_STRING ")\n");
	printf("Usage\n");
	printf("\ttest-stress");
#ifdef BUILD_AS_PLUGINS
	printf(" [-p pluginPath]");
#endif
	printf(" <PATH>\n");
	printf("\n");
	exit(1);
}

class StatusMonitor : public uscxml::InterpreterMonitor {
	void beforeTakingTransitions(uscxml::Interpreter interpreter, const Arabica::XPath::NodeSet<std::string>& transitions) {
		lastTransitionAt = time(NULL);
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

	HTTPServer::getInstance(8088, 8089);
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
			uscxml::Factory::setDefaultPluginPath(optarg);
			break;
		case '?':
			break;
		default:
			printUsageAndExit();
			break;
		}
	}

#if 0
	while(true) {
		Interpreter interpreter = Interpreter::fromURI("/Users/sradomski/Documents/TK/Code/uscxml/test/w3c/ecma/test235.scxml");
		interpreter.interpret();
	}
#else

	DirectoryWatch* watcher = new DirectoryWatch(argv[optind], true);
	watcher->updateEntries(true);
	std::map<std::string, struct stat> entries = watcher->getAllEntries();

	StatusMonitor vm;

	std::map<std::string, struct stat>::iterator entryIter = entries.begin();
	while(entryIter != entries.end()) {
		if (!boost::ends_with(entryIter->first, ".scxml")) {
			entryIter++;
			continue;
		}

		startedAt = time(NULL);
		lastTransitionAt = time(NULL);

		LOG(INFO) << "Processing " << entryIter->first;
		Interpreter interpreter = Interpreter::fromURL(std::string(argv[optind]) + PATH_SEPERATOR + entryIter->first);
		if (interpreter) {
//			interpreter.setCmdLineOptions(argc, argv);

			interpreter.addMonitor(&vm);

			interpreter.start();
			int now = time(NULL);
			while(now - startedAt < 20 && now - lastTransitionAt < 2) {
				// let the interpreter run for a bit
				tthread::this_thread::sleep_for(tthread::chrono::seconds(1));
				now = time(NULL);
			}

		}
		entryIter++;
	}

	delete watcher;
#endif
	return EXIT_SUCCESS;
}