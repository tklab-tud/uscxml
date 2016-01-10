#include "uscxml/config.h"
#include "uscxml/Interpreter.h"
#include "uscxml/debug/Complexity.h"
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
	printf(" [-a {ASPECTS}] [-lN]");
#ifdef BUILD_AS_PLUGINS
	printf(" [-p pluginPath]");
#endif
	printf(" [URL]");
	printf("\n");
	printf("Options\n");
	printf("\t-a {ASPECTS} : analyze with regard to comma seperated aspects\n");
	printf("\t   'issues'     - find common pitfalls and syntactical errors\n");
	printf("\t   'metrics'    - print metrics about the state-chart's complexity\n");
	printf("\t-lN          : Set loglevel to N\n");
	printf("\n");
	exit(1);
}

int main(int argc, char** argv) {
	using namespace uscxml;

	std::string pluginPath;
	std::string inputFile;
	std::list<std::string> aspects;

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
		{"aspect",        optional_argument, 0, 'a'},
		{"loglevel",      required_argument, 0, 'l'},
		{0, 0, 0, 0}
	};

	// parse global options
	int optionInd = 0;
	int option;
	for (;;) {
		option = getopt_long_only(argc, argv, "a:p:l:h", longOptions, &optionInd);
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
		case 'a':
			aspects = InterpreterImpl::tokenize(optarg, ',');
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
		if (aspects.size() == 0 || std::find(aspects.begin(), aspects.end(), "issues") != aspects.end()) {
			std::list<InterpreterIssue> issues = interpreter.validate();
			for (std::list<InterpreterIssue>::iterator issueIter = issues.begin(); issueIter != issues.end(); issueIter++) {
				std::cout << *issueIter << std::endl;
			}
		}

		if (aspects.size() == 0 || std::find(aspects.begin(), aspects.end(), "metrics") != aspects.end()) {

			Arabica::XPath::NodeSet<std::string> states = interpreter.getNodeSetForXPath("//" + interpreter.getNameSpaceInfo().xpathPrefix + "state");
			Arabica::XPath::NodeSet<std::string> final = interpreter.getNodeSetForXPath("//" + interpreter.getNameSpaceInfo().xpathPrefix + "final");
			Arabica::XPath::NodeSet<std::string> parallels = interpreter.getNodeSetForXPath("//" + interpreter.getNameSpaceInfo().xpathPrefix + "parallel");
			Arabica::XPath::NodeSet<std::string> shallowHistories = interpreter.getNodeSetForXPath("//" + interpreter.getNameSpaceInfo().xpathPrefix + "history[@type='shallow']");
			shallowHistories.push_back(interpreter.getNodeSetForXPath("//" + interpreter.getNameSpaceInfo().xpathPrefix + "history[not(@type)]"));
			Arabica::XPath::NodeSet<std::string> deepHistories = interpreter.getNodeSetForXPath("//" + interpreter.getNameSpaceInfo().xpathPrefix + "history[@type='deep']");
			Arabica::XPath::NodeSet<std::string> transitions = interpreter.getNodeSetForXPath("//" + interpreter.getNameSpaceInfo().xpathPrefix + "transition");

			std::cout << "### Number of XML elements" << std::endl;
			std::cout << "#   <state> + <final> + <parallel> + <history>" << std::endl;
			std::cout << "nr_states: " << (states.size() + final.size() + parallels.size() + shallowHistories.size() + deepHistories.size()) << std::endl;
			std::cout << "#   <parallel>" << std::endl;
			std::cout << "nr_parallel: " << parallels.size() << std::endl;
			std::cout << "#   <history type=\"flat\">" << std::endl;
			std::cout << "nr_hist_flat: " << shallowHistories.size() << std::endl;
			std::cout << "#   <history type=\"deep\">" << std::endl;
			std::cout << "nr_hist_deep: " << deepHistories.size() << std::endl;
			std::cout << "#   <transition>" << std::endl;
			std::cout << "nr_trans: " << transitions.size() << std::endl;
			std::cout << "#" << std::endl;


			std::cout << "### Transition Histogram: number of transitions, number of active configurations" << std::endl;

			size_t numberOfLegalConfs = 0;
			size_t lastBin = 0;
			std::cout << "th: ";
			std::string seperator = "";
			std::map<size_t, size_t> histogram = Complexity::getTransitionHistogramm(interpreter.getDocument().getDocumentElement());
			for (std::map<size_t, size_t>::iterator binIter = histogram.begin(); binIter != histogram.end(); binIter++) {
				while (binIter->first > lastBin) {
					lastBin++;
					std::cout << seperator << "0";
					seperator = ", ";
				}
				std::cout << seperator << binIter->second;
				seperator = ", ";
				numberOfLegalConfs += binIter->second;
				lastBin = binIter->first + 1;
			}
			std::cout << std::endl << "#" << std::endl;


			std::stringstream transPowerSetSS;
			std::string transPowerSetSeperator = "";
			for (std::map<size_t, size_t>::reverse_iterator binIter = histogram.rbegin(); binIter != histogram.rend(); binIter++) {
				transPowerSetSS << transPowerSetSeperator << binIter->second << " * " << "2**" << binIter->first;
				transPowerSetSeperator = " + ";
			}
			std::cout << "# Sum of Powersets:" << std::endl;
			std::cout << "ps_sum: " << transPowerSetSS.str() << std::endl;
			std::cout << "#" << std::endl;

			std::cout << "### Upper bounds:" << std::endl;
			std::cout << "# \tActive configurations: " << std::endl;
			std::cout << "up_ac: " << numberOfLegalConfs << std::endl;
			std::cout << "# \tGlobal configurations: " << std::endl;
			std::cout << "up_gc: " << Complexity::stateMachineComplexity(interpreter) << std::endl;

			std::cout << "# \tGlobal configurations (no history): " << std::endl;
			std::cout << "up_gcnh: " << Complexity::stateMachineComplexity(interpreter, uscxml::Complexity::IGNORE_HISTORY) << std::endl;

			std::cout << "# \tGlobal configurations (no nested data): " << std::endl;
			std::cout << "up_gcnd: " << Complexity::stateMachineComplexity(interpreter, uscxml::Complexity::IGNORE_NESTED_DATA) << std::endl;

			std::cout << "# \tGlobal configurations (no unreachable): " << std::endl;
			std::cout << "up_gcnu: " << Complexity::stateMachineComplexity(interpreter, uscxml::Complexity::IGNORE_UNREACHABLE) << std::endl;

			std::cout << "# \tGlobal configurations (no nested data, no history): " << std::endl;
			std::cout << "up_gcnhd: " << Complexity::stateMachineComplexity(interpreter, uscxml::Complexity::IGNORE_HISTORY | uscxml::Complexity::IGNORE_NESTED_DATA) << std::endl;

			std::cout << "# \tGlobal configurations (no history, no unreachable): " << std::endl;
			std::cout << "up_gcnhu: " << Complexity::stateMachineComplexity(interpreter, uscxml::Complexity::IGNORE_HISTORY | uscxml::Complexity::IGNORE_UNREACHABLE) << std::endl;

			std::cout << "# \tGlobal configurations (no nested data, no unreachable): " << std::endl;
			std::cout << "up_gcndu: " << Complexity::stateMachineComplexity(interpreter, uscxml::Complexity::IGNORE_NESTED_DATA | uscxml::Complexity::IGNORE_UNREACHABLE) << std::endl;

			std::cout << "# \tGlobal configurations (no nested data, no history, no unreachable): " << std::endl;
			std::cout << "up_gcnhdu: " << Complexity::stateMachineComplexity(interpreter, uscxml::Complexity::IGNORE_HISTORY | uscxml::Complexity::IGNORE_NESTED_DATA | uscxml::Complexity::IGNORE_UNREACHABLE) << std::endl;
		}
	} catch (Event e) {
		std::cout << e << std::endl;
	}

	return EXIT_SUCCESS;
}