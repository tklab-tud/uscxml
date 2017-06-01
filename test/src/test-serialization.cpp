//#define protected public

#include "uscxml/config.h"
#include "uscxml/Interpreter.h"
#include "uscxml/interpreter/InterpreterImpl.h"
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

//class StatusMonitor : public uscxml::InterpreterMonitor {
class StatusMonitor : public uscxml::StateTransitionMonitor {
	void beforeTakingTransition(uscxml::Interpreter& interpreter, const XERCESC_NS::DOMElement* transition) {
		lastTransitionAt = time(NULL);
	}

};

void printUsageAndExit() {
	printf("test-serialization version " USCXML_VERSION " (" CMAKE_BUILD_TYPE " build - " CMAKE_COMPILER_STRING ")\n");
	printf("Usage\n");
	printf("\ttest-serialization");
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
	vm.copyToInvokers(true);

	std::map<std::string, struct stat>::iterator entryIter = entries.begin();
	while(entryIter != entries.end()) {
		if (!boost::ends_with(entryIter->first, ".scxml") ||
		        entryIter->first.find("sub") != std::string::npos ||
		        entryIter->first.find("test415.scxml") != std::string::npos ||
		        entryIter->first.find("test329.scxml") != std::string::npos ||
		        entryIter->first.find("test326.scxml") != std::string::npos ||
		        entryIter->first.find("test307.scxml") != std::string::npos ||
		        entryIter->first.find("test301.scxml") != std::string::npos ||
		        entryIter->first.find("test230.scxml") != std::string::npos ||
		        entryIter->first.find("test250.scxml") != std::string::npos ||
		        entryIter->first.find("test178.scxml") != std::string::npos) {
			entryIter++;
			continue;
		}

		startedAt = time(NULL);
		lastTransitionAt = time(NULL);

		std::string sourceXML = std::string(argv[optind]) + PATH_SEPERATOR + entryIter->first;
		sourceXML = "/Users/sradomski/Documents/TK/Code/uscxml/test/w3c/ecma/test557.scxml";

		Interpreter interpreter = Interpreter::fromURL(sourceXML);
		LOGD(USCXML_INFO) << "Processing " << interpreter.getImpl()->getBaseURL() << std::endl;
		if (interpreter) {

			interpreter.addMonitor(&vm);
			std::string serializedState;

RESTART_WITH_STATE:
			InterpreterState state = InterpreterState::USCXML_UNDEF;
			int now = time(NULL);

			try {
#if 1
				if (serializedState.size() > 0) {
					Interpreter interpreter = Interpreter::fromURL(sourceXML);
					interpreter.deserialize(serializedState);
				}
#endif
//                while(state != USCXML_FINISHED && now - startedAt < 20 && now - lastTransitionAt < 2) {

				while(state != USCXML_FINISHED) {
					state = interpreter.step();

#if 1
					if (state == USCXML_MACROSTEPPED) {
//						assert(!interpreter.getImpl()->_internalQueue.dequeue(0));
						serializedState = interpreter.serialize();
//                        std::cout << serializedState << std::endl;
						goto RESTART_WITH_STATE;
					}
#endif

					now = time(NULL);
				}
				assert(interpreter.isInState("pass"));
			} catch (ErrorEvent e) {
				LOGD(USCXML_ERROR) << e;
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
