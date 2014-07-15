#include "uscxml/config.h"
#include "uscxml/Interpreter.h"
#include "uscxml/DOMUtils.h"
#include "uscxml/debug/SCXMLDotWriter.h"
#include <glog/logging.h>

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
	printf(" [-dN_0] URL");
	printf(" [[-dN_1] state_id1] .. [[-dN_M] state_idM]");
	printf("\n");
	printf("Options\n");
	printf("\tURL       : URL of SCXML document\n");
	printf("\t-d        : depth below anchor node (INF per default)\n");
	printf("\tstate_id  : anchor node state id (topmost scxml element per default)\n");
	printf("\n");
	exit(1);
}

int currOpt = 1;

int consumeDepthOption(int argc, char** argv) {
	std::string test = argv[currOpt];
	if (boost::starts_with(test, "-")) {
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

	return -1;
}

int main(int argc, char** argv) {

	// setup logging
	google::LogToStderr();
	google::InitGoogleLogging(argv[0]);

	std::list<SCXMLDotWriter::StateAnchor> stateAnchors;

	if (argc < 2)
		printUsageAndExit(argv[0]);

	try {
		// see if there is an initial depth given for root
		int depth = consumeDepthOption(argc, argv);
		if (depth >= 0) {
			SCXMLDotWriter::StateAnchor anchor;
			anchor.depth = depth;
			stateAnchors.push_back(anchor);
		}

		// current option has to be the interpreter's name
		URL inputFile(argv[currOpt++]);
		Interpreter interpreter = Interpreter::fromURI(inputFile);

		for (; currOpt < argc; currOpt++) {
			SCXMLDotWriter::StateAnchor anchor;
			depth = consumeDepthOption(argc, argv);

			if (depth >= 0) {
				anchor.depth = depth;
			}

			if (argc > currOpt) {
				std::string expr(argv[currOpt++]);
				anchor.element = interpreter.getImpl()->getState(expr);
			} else {
				printUsageAndExit(argv[0]);
			}

			stateAnchors.push_back(anchor);
		}

		SCXMLDotWriter::toDot("machine.dot", interpreter, stateAnchors);

	} catch(Event e) {
		std::cerr << e << std::cout;
	}

	return EXIT_SUCCESS;
}
