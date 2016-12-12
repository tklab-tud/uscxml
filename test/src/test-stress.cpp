#include "uscxml/config.h"
#include "uscxml/Interpreter.h"
//#include "uscxml/Factory.h"
#include "uscxml/server/HTTPServer.h"

#include "uscxml/interpreter/Logging.h"

#include "uscxml/plugins/invoker/dirmon/DirMonInvoker.h"
#include <boost/algorithm/string.hpp>

#ifdef _WIN32
#include "XGetopt.h"
#include "XGetopt.cpp"
#endif

int startedAt;
int lastTransitionAt;

class StatusMonitor : public uscxml::InterpreterMonitor {
	void beforeTakingTransition(uscxml::Interpreter& interpreter, const XERCESC_NS::DOMElement* transition) {
		lastTransitionAt = time(NULL);
	}

};

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

int main(int argc, char** argv) {
	using namespace uscxml;

	if (argc < 2) {
		printUsageAndExit();
	}

	HTTPServer::getInstance(8188, 8189);
#ifndef _WIN32
	opterr = 0;
#endif
	int option;
	while ((option = getopt(argc, argv, "vl:p:")) != -1) {
		switch(option) {
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

		Interpreter interpreter = Interpreter::fromURL(std::string(argv[optind]) + PATH_SEPERATOR + entryIter->first);
//        Interpreter interpreter = Interpreter::fromURL("/Users/sradomski/Documents/TK/Code/uscxml/test/w3c/ecma/test422.scxml");
		LOGD(USCXML_INFO) << "Processing " << interpreter.getImpl()->getBaseURL();
		if (interpreter) {

			interpreter.addMonitor(&vm);

			InterpreterState state = InterpreterState::USCXML_UNDEF;
			int now = time(NULL);

			try {
				while(state != USCXML_FINISHED && now - startedAt < 20 && now - lastTransitionAt < 2) {
//                while(state != USCXML_FINISHED) {
					state = interpreter.step(200);
					now = time(NULL);
				}
			} catch (...) {}
		}
		entryIter++;

		// forever
//        if (entryIter == entries.end()) {
//            entryIter = entries.begin();
//        }
	}

	delete watcher;

	return EXIT_SUCCESS;
}
