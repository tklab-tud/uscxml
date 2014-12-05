#include "uscxml/config.h"
#include "uscxml/Interpreter.h"
#include "uscxml/transform/ChartToFlatSCXML.h"
#include "uscxml/transform/ChartToPromela.h"
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

class VerboseMonitor : public uscxml::InterpreterMonitor {
	void onStableConfiguration(uscxml::Interpreter interpreter) {
		printConfig(interpreter.getConfiguration());
	}

	void beforeProcessingEvent(uscxml::Interpreter interpreter, const uscxml::Event& event) {
		std::cerr << "Event: " << event.name << std::endl;
	}

	void beforeCompletion(uscxml::Interpreter interpreter) {
		printConfig(interpreter.getConfiguration());
	}

	void printConfig(const Arabica::XPath::NodeSet<std::string>& config) {
		std::string seperator;
		std::cerr << "Config: {";
		for (int i = 0; i < config.size(); i++) {
			std::cerr << seperator << ATTR_CAST(config[i], "id");
			seperator = ", ";
		}
		std::cerr << "}" << std::endl;
	}
};

void printUsageAndExit(const char* progName) {
	// remove path from program name
	std::string progStr(progName);
	if (progStr.find_last_of(PATH_SEPERATOR) != std::string::npos) {
		progStr = progStr.substr(progStr.find_last_of(PATH_SEPERATOR) + 1, progStr.length() - (progStr.find_last_of(PATH_SEPERATOR) + 1));
	}

	printf("%s version " USCXML_VERSION " (" CMAKE_BUILD_TYPE " build - " CMAKE_COMPILER_STRING ")\n", progStr.c_str());
	printf("Usage\n");
	printf("\t%s", progStr.c_str());
	printf(" [-t pml|flat] [-v] [-lN]");
#ifdef BUILD_AS_PLUGINS
	printf(" [-p pluginPath]");
#endif
	printf(" [-i URL] [-o FILE]");
	printf("\n");
	printf("Options\n");
	printf("\t-t flat   : flatten to SCXML state-machine\n");
	printf("\t-t pml    : convert to spin/promela program\n");
	printf("\t-v        : be verbose\n");
	printf("\t-lN       : Set loglevel to N\n");
	printf("\t-i URL    : Input file (defaults to STDIN)\n");
	printf("\t-o FILE   : Output file (defaults to STDOUT)\n");
	printf("\n");
	exit(1);
}

int main(int argc, char** argv) {
	using namespace uscxml;

	bool verbose = false;
	std::string outType;
	std::string pluginPath;
	std::string inputFile;
	std::string outputFile;

#if defined(HAS_SIGNAL_H) && !defined(WIN32)
	signal(SIGPIPE, SIG_IGN);
#endif

	// setup logging
	google::LogToStderr();
	google::InitGoogleLogging(argv[0]);

	optind = 0;
	opterr = 0;

	struct option longOptions[] = {
		{"verbose",       no_argument,       0, 'v'},
		{"type",          required_argument, 0, 't'},
		{"plugin-path",   required_argument, 0, 'p'},
		{"input-file",    required_argument, 0, 'i'},
		{"output-file",    required_argument, 0, 'o'},
		{"loglevel",      required_argument, 0, 'l'},
		{0, 0, 0, 0}
	};

	// parse global options
	int optionInd = 0;
	int option;
	for (;;) {
		option = getopt_long_only(argc, argv, "+vp:t:i:o:l:", longOptions, &optionInd);
		if (option == -1) {
			break;
		}
		switch(option) {
		// cases without short option
		case 0: {
			break;
		}
		// cases with short-hand options
		case 'v':
			verbose = true;
			break;
		case 't':
			outType = optarg;
			break;
		case 'p':
			pluginPath = optarg;
			break;
		case 'i':
			inputFile = optarg;
			break;
		case 'o':
			outputFile = optarg;
			break;
		case 'l':
			break;
		case '?': {
			break;
		}
		default:
			break;
		}
	}

	if (outType.length() == 0 && outputFile.length() > 0) {
		// try to get type from outfile extension
		size_t dotPos = outputFile.find_last_of(".");
		if (dotPos != std::string::npos) {
			outType= outputFile.substr(dotPos + 1);
		}
	}
	
	if (outType.length() == 0)
		printUsageAndExit(argv[0]);

	if (outType != "flat" && outType != "scxml" && outType != "pml")
		printUsageAndExit(argv[0]);

	// register plugins
	if (pluginPath.length() > 0) {
		Factory::setDefaultPluginPath(pluginPath);
	}

	// start HTTP server
	HTTPServer::getInstance(30444, 30445, NULL);

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
			interpreter = Interpreter::fromURI(inputFile);
		}
		if (!interpreter) {
			LOG(ERROR) << "Cannot create interpreter from " << inputFile;
			exit(EXIT_FAILURE);
		}

		if (outType == "pml") {
			if (outputFile.size() == 0 || outputFile == "-") {
				ChartToPromela::transform(interpreter).writeTo(std::cout);
			} else {
				std::ofstream outStream;
				outStream.open(outputFile.c_str());
				ChartToPromela::transform(interpreter).writeTo(outStream);
				outStream.close();
			}
			exit(EXIT_SUCCESS);

//			Interpreter flatInterpreter = ChartToPromela::transform(interpreter);
//
//			if (outputFile.size() == 0 || outputFile == "-") {
//				ChartToPromela::writeProgram(std::cout, flatInterpreter);
//			} else {
//				std::ofstream outStream;
//				outStream.open(outputFile.c_str());
//				ChartToPromela::writeProgram(outStream, flatInterpreter);
//				outStream.close();
//			}
//			exit(EXIT_SUCCESS);
		}

		if (outType == "scxml" || outType == "flat") {
			if (outputFile.size() == 0 || outputFile == "-") {
				ChartToFlatSCXML::transform(interpreter).writeTo(std::cout);
			} else {
				std::ofstream outStream;
				outStream.open(outputFile.c_str());
				ChartToFlatSCXML::transform(interpreter).writeTo(outStream);
				outStream.close();
			}
			exit(EXIT_SUCCESS);
		}
	} catch (Event e) {
		std::cout << e << std::endl;
	}

	return EXIT_SUCCESS;
}