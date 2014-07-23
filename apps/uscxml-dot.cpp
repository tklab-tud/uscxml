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

int32_t consumeNumericOption(int argc, char** argv, const std::string& name, int32_t defaultVal) {
	std::string test = argv[currOpt];
	if (boost::starts_with(test, std::string("-") + name)) {
		int value = 0;
		if (test.size() > 2) {
			// no space before value
			value = strTo<int>(test.substr(2, test.size() - 2));
		} else {
			// space before value
			if (argc > currOpt) {
				std::string tmp = argv[++currOpt];
				value = strTo<int>(tmp);
			} else {
				printUsageAndExit(argv[0]);
			}
		}
		currOpt++;
		return value;
	}

	return defaultVal;
}

int main(int argc, char** argv) {

	// setup logging
	google::LogToStderr();
	google::InitGoogleLogging(argv[0]);


	if (argc < 2)
		printUsageAndExit(argv[0]);

	std::list<SCXMLDotWriter::StateAnchor> stateAnchors;
	SCXMLDotWriter::StateAnchor currAnchor;

	int option;
	while ((option = getopt(argc, argv, "d:t:")) != -1) {
		switch(option) {
		case 'd':
			currAnchor.childDepth = strTo<int32_t>(optarg);
			break;
		case 't':
			currAnchor.transDepth = strTo<int32_t>(optarg);
			break;
		case 'e': {
			std::string edgeType(optarg);
			if (edgeType == "target") {
				currAnchor.type = SCXMLDotWriter::PORT_TARGET;
			} else if (edgeType == "event") {
				currAnchor.type = SCXMLDotWriter::PORT_EVENT;
			} else if (edgeType == "transition") {
				currAnchor.type = SCXMLDotWriter::PORT_TRANSITION;
			} else {
				printUsageAndExit(argv[0]);
			}
			break;
		}
		default:
			break;
		}
	}

	if (currAnchor)
		stateAnchors.push_back(currAnchor);

	try {
		// current option has to be the interpreter's name
		URL inputFile(argv[optind]);
		Interpreter interpreter = Interpreter::fromURI(inputFile);
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
				stateAnchors.push_back(currAnchor);
			}

			currAnchor = SCXMLDotWriter::StateAnchor();
		}

		std::string outName = inputFile.file() + ".dot";
		SCXMLDotWriter::toDot(outName, interpreter, stateAnchors);

	} catch(Event e) {
		std::cerr << e << std::cout;
	}

	return EXIT_SUCCESS;
}
