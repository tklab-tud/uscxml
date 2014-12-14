#include "uscxml/config.h"
#include "uscxml/Interpreter.h"
#include "uscxml/DOMUtils.h"
#include "uscxml/debug/SCXMLDotWriter.h"
#include <glog/logging.h>
#include "getopt.h"

#include "uscxml/Factory.h"
#include <boost/algorithm/string.hpp>


using namespace uscxml;

void printUsageAndExit(const char* progName) {
	// remove path from program name
	std::string progStr(progName);
	if (progStr.find_last_of(PATH_SEPERATOR) != std::string::npos) {
		progStr = progStr.substr(progStr.find_last_of(PATH_SEPERATOR) + 1, progStr.length() - (progStr.find_last_of(PATH_SEPERATOR) + 1));
	}

	printf("%s version " USCXML_VERSION " (" CMAKE_BUILD_TYPE " build - " CMAKE_COMPILER_STRING ")\n", progStr.c_str());
	printf("Usage\n");
	printf("\t%s", progStr.c_str());
	printf(" [-eTYPE] [-dN] [-tN] URL");
	printf(" [[-dN] [-tN] [-eTYPE] state_id1] .. [[-dN] [-tN] [-eTYPE] state_idM]");
	printf("\n");
	printf("Options\n");
	printf("\tURL       : URL of SCXML document\n");
	printf("\t-e TYPE   : type of edges to use:\n");
	printf("\t             'target' - aggregate per target node (default)\n");
	printf("\t             'event' - aggregate per event name\n");
	printf("\t             'transition' no aggregation, display each transition\n");
	printf("\t-d        : depth below anchor node (INF per default)\n");
	printf("\t-t        : transition depth below anchor (INF per default)\n");
	printf("\tstate_id  : anchor node state id (topmost scxml element per default)\n");
	printf("\n");
	exit(1);
}

int currOpt = 1;

int main(int argc, char** argv) {

	// setup logging
	google::LogToStderr();
	google::InitGoogleLogging(argv[0]);


	if (argc < 2)
		printUsageAndExit(argv[0]);

	std::list<SCXMLDotWriter::StateAnchor> stateAnchors;
	SCXMLDotWriter::StateAnchor rootAnchor;
	SCXMLDotWriter::StateAnchor currAnchor;

	int option;
	while ((option = getopt(argc, argv, "d:t:e:")) != -1) {
		switch(option) {
		case 'd':
			rootAnchor.childDepth = strTo<int32_t>(optarg);
			break;
		case 't':
			rootAnchor.transDepth = strTo<int32_t>(optarg);
			break;
		case 'e': {
			std::string edgeType(optarg);
			if (edgeType == "target") {
				rootAnchor.type = SCXMLDotWriter::PORT_TARGET;
			} else if (edgeType == "event") {
				rootAnchor.type = SCXMLDotWriter::PORT_EVENT;
			} else if (edgeType == "transition") {
				rootAnchor.type = SCXMLDotWriter::PORT_TRANSITION;
			} else {
				printUsageAndExit(argv[0]);
			}
			break;
		}
		default:
			break;
		}
	}

	if (rootAnchor)
		stateAnchors.push_back(rootAnchor);

	try {
		// current option has to be the interpreter's name
		URL inputFile(argv[optind]);
		Interpreter interpreter = Interpreter::fromURL(inputFile.asString());
		optind++;

		while(optind < argc) {
			// are
			while ((option = getopt(argc, argv, "d:t:")) != -1) {
				switch(option) {
				case 'd':
					currAnchor.childDepth = strTo<int32_t>(optarg);
					break;
				case 't':
					currAnchor.transDepth = strTo<int32_t>(optarg);
					break;
				default:
					break;
				}
			}
			if (argc > optind) {
				std::string expr(argv[optind++]);
				currAnchor.element = interpreter.getImpl()->getState(expr);
			} else {
				printUsageAndExit(argv[0]);
			}

			if (currAnchor) {
				currAnchor.type = rootAnchor.type;
				stateAnchors.push_back(currAnchor);
			}

			currAnchor = SCXMLDotWriter::StateAnchor();
		}

		std::string outName;
		if (boost::starts_with("file", inputFile.scheme())) {
			outName = inputFile.path() + ".dot";
		} else {
			outName = inputFile.file() + ".dot";
		}

		SCXMLDotWriter::toDot(outName, interpreter, stateAnchors);

	} catch(Event e) {
		std::cerr << e << std::cout;
	}

	return EXIT_SUCCESS;
}
