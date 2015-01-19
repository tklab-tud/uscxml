#include "uscxml/config.h"
#include "uscxml/Interpreter.h"
#include "uscxml/transform/ChartToFSM.h"
#include "uscxml/DOMUtils.h"
#include <glog/logging.h>
#include <fstream>
#include <iostream>

#include "uscxml/Factory.h"
#include "uscxml/server/HTTPServer.h"
#include "getopt.h"

#ifdef HAS_SIGNAL_H
#include <signal.h>
#endif

#ifdef HAS_EXECINFO_H
#include <execinfo.h>
#endif

#ifdef HAS_DLFCN_H
#include <dlfcn.h>
#endif

#define ANNOTATE(envKey, annotationParam) \
envVarIsTrue(envKey) || std::find(annotations.begin(), annotations.end(), annotationParam) != annotations.end()

void printUsageAndExit(const char* progName) {
	// remove path from program name
	std::string progStr(progName);
	if (progStr.find_last_of(PATH_SEPERATOR) != std::string::npos) {
		progStr = progStr.substr(progStr.find_last_of(PATH_SEPERATOR) + 1, progStr.length() - (progStr.find_last_of(PATH_SEPERATOR) + 1));
	}

	printf("%s version " USCXML_VERSION " (" CMAKE_BUILD_TYPE " build - " CMAKE_COMPILER_STRING ")\n", progStr.c_str());
	printf("Usage\n");
	printf("\t%s", progStr.c_str());
#ifdef BUILD_AS_PLUGINS
	printf(" [-p pluginPath]");
#endif
	printf(" [URL]");
	printf("\n");
	exit(1);
}

int main(int argc, char** argv) {
	using namespace uscxml;

	std::string outType;
	std::string pluginPath;
	std::string inputFile;
	std::string outputFile;
	std::list<std::string> annotations;
	
#if defined(HAS_SIGNAL_H) && !defined(WIN32)
	signal(SIGPIPE, SIG_IGN);
#endif

	// setup logging
	google::LogToStderr();
	google::InitGoogleLogging(argv[0]);

	optind = 0;
	opterr = 0;

	struct option longOptions[] = {
		{"help",   required_argument, 0, 'p'},
		{"plugin-path",   required_argument, 0, 'p'},
		{"loglevel",      required_argument, 0, 'l'},
		{0, 0, 0, 0}
	};

	// parse global options
	int optionInd = 0;
	int option;
	for (;;) {
		option = getopt_long_only(argc, argv, "p:l:h", longOptions, &optionInd);
		if (option == -1) {
			break;
		}
		switch(option) {
		// cases without short option
		case 0: {
			break;
		}
		// cases with short-hand options
		case 'p':
			pluginPath = optarg;
			break;
		case 'l':
			break;
		case 'h':
		case '?': {
			printUsageAndExit(argv[0]);
			break;
		}
		default:
			break;
		}
	}

	if (optind < argc) {
		inputFile = argv[optind];
	}
	
	// register plugins
	if (pluginPath.length() > 0) {
		Factory::setDefaultPluginPath(pluginPath);
	}

	// start HTTP server
	HTTPServer::getInstance(31444, 31445, NULL);

	Interpreter interpreter;
	try {
		if (inputFile.size() == 0 || inputFile == "-") {
			LOG(INFO) << "Reading SCXML from STDIN";
			std::stringstream ss;
			std::string line;
			while (std::getline(std::cin, line)) {
				ss << line;
			}
			URL tmp("anonymous.scxml");
			tmp.toAbsoluteCwd();
			interpreter = Interpreter::fromXML(ss.str(), tmp);
		} else {
			interpreter = Interpreter::fromURL(inputFile);
		}
		if (!interpreter) {
			LOG(ERROR) << "Cannot create interpreter from " << inputFile;
			exit(EXIT_FAILURE);
		}

		// analyze here
		Arabica::XPath::NodeSet<std::string> states = interpreter.getNodeSetForXPath("//" + interpreter.getNameSpaceInfo().xpathPrefix + "state");
		Arabica::XPath::NodeSet<std::string> final = interpreter.getNodeSetForXPath("//" + interpreter.getNameSpaceInfo().xpathPrefix + "final");
		Arabica::XPath::NodeSet<std::string> parallels = interpreter.getNodeSetForXPath("//" + interpreter.getNameSpaceInfo().xpathPrefix + "parallel");
		Arabica::XPath::NodeSet<std::string> shallowHistories = interpreter.getNodeSetForXPath("//" + interpreter.getNameSpaceInfo().xpathPrefix + "history[@type='shallow']");
		shallowHistories.push_back(interpreter.getNodeSetForXPath("//" + interpreter.getNameSpaceInfo().xpathPrefix + "history[not(@type)]"));
		Arabica::XPath::NodeSet<std::string> deepHistories = interpreter.getNodeSetForXPath("//" + interpreter.getNameSpaceInfo().xpathPrefix + "history[@type='deep']");
		Arabica::XPath::NodeSet<std::string> transitions = interpreter.getNodeSetForXPath("//" + interpreter.getNameSpaceInfo().xpathPrefix + "transition");

		std::cout << "# Number of elements" << std::endl;
		std::cout << "nr_states: " << (states.size() + final.size() + parallels.size()) << std::endl;
		std::cout << "nr_parallel: " << parallels.size() << std::endl;
		std::cout << "nr_hist_flat: " << shallowHistories.size() << std::endl;
		std::cout << "nr_hist_deep: " << deepHistories.size() << std::endl;
		std::cout << "nr_trans: " << transitions.size() << std::endl;

		
		std::cout << "# Transition Histogram: number of transitions, number of active configurations" << std::endl;

		size_t numberOfLegalConfs = 0;
		size_t lastBin = 0;
		std::map<size_t, size_t> histogram = Complexity::getTransitionHistogramm(interpreter.getDocument().getDocumentElement());
		for (std::map<size_t, size_t>::iterator binIter = histogram.begin(); binIter != histogram.end(); binIter++) {
			while (binIter->first > lastBin) {
				std::cout << "th: " << toStr(lastBin++) << ", 0" << std::endl;
			}
			std::cout << "th: " << toStr(binIter->first) << ", " << binIter->second << std::endl;
			numberOfLegalConfs += binIter->second;
			lastBin = binIter->first + 1;
		}

		std::stringstream transPowerSetSS;
		std::string transPowerSetSeperator = "";
		for (std::map<size_t, size_t>::reverse_iterator binIter = histogram.rbegin(); binIter != histogram.rend(); binIter++) {
			transPowerSetSS << transPowerSetSeperator << binIter->second << " * " << "2**" << binIter->first;
			transPowerSetSeperator = " + ";
		}
		std::cout << "# Sum of Powersets:" << std::endl;
		std::cout << "ps_sum: " << transPowerSetSS.str() << std::endl;
		std::cout << "# Upper bounds:" << std::endl;
		std::cout << "# \tActive configurations: " << std::endl;
		std::cout << "up_ac: " << numberOfLegalConfs << std::endl;
		std::cout << "# \tGlobal configurations: " << std::endl;
		std::cout << "up_gc: " << Complexity::stateMachineComplexity(interpreter.getDocument().getDocumentElement()) << std::endl;
		
		std::cout << "# \tGlobal configurations (no history): " << std::endl;
		std::cout << "up_gcnh: " << Complexity::stateMachineComplexity(interpreter.getDocument().getDocumentElement(), uscxml::Complexity::IGNORE_HISTORY) << std::endl;

		std::cout << "# \tGlobal configurations (no nested data): " << std::endl;
		std::cout << "up_gcnd: " << Complexity::stateMachineComplexity(interpreter.getDocument().getDocumentElement(), uscxml::Complexity::IGNORE_NESTED_DATA) << std::endl;
		
		std::cout << "# \tGlobal configurations (no nested data, no history): " << std::endl;
		std::cout << "up_gcnhd: " << Complexity::stateMachineComplexity(interpreter.getDocument().getDocumentElement(), uscxml::Complexity::IGNORE_HISTORY_AND_NESTED_DATA) << std::endl;

	} catch (Event e) {
		std::cout << e << std::endl;
	}

	return EXIT_SUCCESS;
}