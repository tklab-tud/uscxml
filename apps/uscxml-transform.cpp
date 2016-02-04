#include "uscxml/config.h"
#include "uscxml/Interpreter.h"
#include "uscxml/transform/ChartToFlatSCXML.h"
#include "uscxml/transform/ChartToC.h"
#include "uscxml/transform/ChartToVHDL.h"
#include "uscxml/transform/ChartToTex.h"
#include "uscxml/transform/ChartToMinimalSCXML.h"
#include "uscxml/transform/ChartToPromela.h"
#include "uscxml/DOMUtils.h"

#include <glog/logging.h>
#include <boost/algorithm/string.hpp>

#include <fstream>
#include <iostream>
#include <map>

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
envVarIsTrue(envKey) || std::find(options.begin(), options.end(), annotationParam) != options.end()

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
	printf(" [-t c|pml|flat|min|tex] [-a {OPTIONS}] [-v] [-lN]");
#ifdef BUILD_AS_PLUGINS
	printf(" [-p pluginPath]");
#endif
	printf(" [-i URL] [-o FILE]");
	printf("\n");
	printf("Options\n");
	printf("\t-t c           : convert to C program\n");
	printf("\t-t pml         : convert to spin/promela program\n");
	printf("\t-t vhdl        : convert to VHDL hardware description\n");
	printf("\t-t flat        : flatten to SCXML state-machine\n");
	printf("\t-t min         : minimize SCXML state-chart\n");
	printf("\t-t tex         : write global state transition table as tex file\n");
	printf("\t-a {OPTIONS}   : annotate SCXML elements with comma seperated options\n");
	printf("\t    priority     - transitions with their priority for transition selection\n");
	printf("\t    exitset      - annotate all transitions with their exit sets\n");
	printf("\t    entryset     - annotate all transitions with their entry sets\n");
	printf("\t    conflicts    - annotate all transitions with their conflicts\n");
	printf("\t    domain       - annotate all transitions with their domain\n");
	printf("\t    step         - global states with their step identifier (-tflat only)\n");
	printf("\t    members      - global transitions with their member transitions per index (-tflat only)\n");
	printf("\t    sends        - transititve number of sends to external queue for global transitions (-tflat only)\n");
	printf("\t    raises       - transititve number of raises to internal queue for global transitions (-tflat only)\n");
	printf("\t    verbose      - comments detailling state changes and transitions for content selection (-tflat only)\n");
	printf("\t    progress     - insert comments documenting progress in dociment (-tmin only)\n");
	printf("\t    nocomment    - surpress the generation of comments in output\n");
	printf("\t-X {PARAMETER} : pass additional parameters to the transformation\n");
	printf("\t    prefix=ID    - prefix all symbols and identifiers with ID (-tc)\n");
	printf("\t-v             : be verbose\n");
	printf("\t-lN            : Set loglevel to N\n");
	printf("\t-i URL         : Input file (defaults to STDIN)\n");
	printf("\t-o FILE        : Output file (defaults to STDOUT)\n");
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
	std::list<std::string> options;
	std::multimap<std::string, std::string> extensions;

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
		{"annotate",      required_argument, 0, 'a'},
		{"param",         required_argument, 0, 'X'},
		{"plugin-path",   required_argument, 0, 'p'},
		{"input-file",    required_argument, 0, 'i'},
		{"output-file",   required_argument, 0, 'o'},
		{"loglevel",      required_argument, 0, 'l'},
		{0, 0, 0, 0}
	};

	// parse global options
	int optionInd = 0;
	int option;
	for (;;) {
		option = getopt_long_only(argc, argv, "+vp:X:t:i:o:l:a:", longOptions, &optionInd);
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
		case 'a':
			options = InterpreterImpl::tokenize(optarg, ',');
			break;
		case 'X': {
			std::list<std::string> extension = InterpreterImpl::tokenize(optarg, '=');
			if (extension.size() != 2)
				printUsageAndExit(argv[0]);
			std::string key = boost::trim_copy(*(extension.begin()));
			std::string value = boost::trim_copy(*(++extension.begin()));
			extensions.insert(std::pair<std::string, std::string>(key, value));
		}
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

	// make sure given annotation options are available in the environment
	if(ANNOTATE("USCXML_ANNOTATE_GLOBAL_STATE_STEP", "step"))
		setenv("USCXML_ANNOTATE_GLOBAL_STATE_STEP", "YES", 1);

	if (ANNOTATE("USCXML_ANNOTATE_GLOBAL_TRANS_PRIO", "priority"))
		setenv("USCXML_ANNOTATE_GLOBAL_TRANS_PRIO", "YES", 1);

	if (ANNOTATE("USCXML_ANNOTATE_VERBOSE_COMMENTS", "verbose"))
		setenv("USCXML_ANNOTATE_VERBOSE_COMMENTS", "YES", 1);

	if (ANNOTATE("USCXML_ANNOTATE_TRANS_EXITSET", "exitset"))
		setenv("USCXML_ANNOTATE_TRANS_EXITSET", "YES", 1);

	if (ANNOTATE("USCXML_ANNOTATE_TRANS_DOMAIN", "domain"))
		setenv("USCXML_ANNOTATE_TRANS_DOMAIN", "YES", 1);

	if (ANNOTATE("USCXML_ANNOTATE_TRANS_CONFLICTS", "conflicts"))
		setenv("USCXML_ANNOTATE_TRANS_CONFLICTS", "YES", 1);

	if (ANNOTATE("USCXML_ANNOTATE_TRANS_ENTRYSET", "entryset"))
		setenv("USCXML_ANNOTATE_TRANS_ENTRYSET", "YES", 1);

	if(ANNOTATE("USCXML_ANNOTATE_GLOBAL_TRANS_MEMBERS", "members"))
		setenv("USCXML_ANNOTATE_GLOBAL_TRANS_MEMBERS", "YES", 1);

	if(ANNOTATE("USCXML_ANNOTATE_GLOBAL_TRANS_SENDS", "sends"))
		setenv("USCXML_ANNOTATE_GLOBAL_TRANS_SENDS", "YES", 1);

	if(ANNOTATE("USCXML_ANNOTATE_GLOBAL_TRANS_RAISES", "raises"))
		setenv("USCXML_ANNOTATE_GLOBAL_TRANS_RAISES", "YES", 1);

	if(ANNOTATE("USCXML_ANNOTATE_PROGRESS", "progress"))
		setenv("USCXML_ANNOTATE_PROGRESS", "YES", 1);

	if(ANNOTATE("USCXML_ANNOTATE_NOCOMMENT", "nocomment"))
		setenv("USCXML_ANNOTATE_NOCOMMENT", "YES", 1);


//	if (outType.length() == 0 && outputFile.length() > 0) {
//		// try to get type from outfile extension
//		size_t dotPos = outputFile.find_last_of(".");
//		if (dotPos != std::string::npos) {
//			outType= outputFile.substr(dotPos + 1);
//		}
//	}

//	if (outType.length() == 0)
//		printUsageAndExit(argv[0]);

	if (outType != "flat" &&
	        outType != "scxml" &&
	        outType != "pml" &&
	        outType != "c" &&
	        outType != "vhdl" &&
	        outType != "min" &&
	        outType != "tex" &&
	        std::find(options.begin(), options.end(), "priority") == options.end() &&
	        std::find(options.begin(), options.end(), "domain") == options.end() &&
	        std::find(options.begin(), options.end(), "conflicts") == options.end() &&
	        std::find(options.begin(), options.end(), "exitset") == options.end() &&
	        std::find(options.begin(), options.end(), "entryset") == options.end())
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
			interpreter = Interpreter::fromURL(inputFile);
		}
		if (!interpreter) {
			LOG(ERROR) << "Cannot create interpreter from " << inputFile;
			exit(EXIT_FAILURE);
		}

		if (verbose) {
			std::list<InterpreterIssue> issues = interpreter.validate();
			for (std::list<InterpreterIssue>::iterator issueIter = issues.begin(); issueIter != issues.end(); issueIter++) {
				std::cerr << *issueIter << std::endl;
			}
		}

		if (outType == "c") {
			Transformer transformer = ChartToC::transform(interpreter);
			transformer.setExtensions(extensions);
			transformer.setOptions(options);
			if (outputFile.size() == 0 || outputFile == "-") {
				transformer.writeTo(std::cout);
			} else {
				std::ofstream outStream;
				outStream.open(outputFile.c_str());
				transformer.writeTo(outStream);
				outStream.close();
			}
			exit(EXIT_SUCCESS);
		}

		if (outType == "vhdl") {
			if (outputFile.size() == 0 || outputFile == "-") {
				ChartToVHDL::transform(interpreter).writeTo(std::cout);
			} else {
				std::ofstream outStream;
				outStream.open(outputFile.c_str());
				ChartToVHDL::transform(interpreter).writeTo(outStream);
				outStream.close();
			}
			exit(EXIT_SUCCESS);
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
		}

		if (outType == "tex") {
			if (outputFile.size() == 0 || outputFile == "-") {
				ChartToTex::transform(interpreter).writeTo(std::cout);
			} else {
				std::ofstream outStream;
				outStream.open(outputFile.c_str());
				ChartToTex::transform(interpreter).writeTo(outStream);
				outStream.close();
			}
			exit(EXIT_SUCCESS);
		}

		if (outType == "flat") {
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

		if (outType == "min") {
			if (outputFile.size() == 0 || outputFile == "-") {
				ChartToMinimalSCXML::transform(interpreter).writeTo(std::cout);
			} else {
				std::ofstream outStream;
				outStream.open(outputFile.c_str());
				ChartToMinimalSCXML::transform(interpreter).writeTo(outStream);
				outStream.close();
			}
			exit(EXIT_SUCCESS);
		}


#if 1
		if (options.size() > 0) {
			ChartToFSM annotater(interpreter);
			if (std::find(options.begin(), options.end(), "priority") != options.end())
				annotater.indexTransitions();
			if (std::find(options.begin(), options.end(), "conflicts") != options.end())
				annotater.annotateConflicts();
			if (std::find(options.begin(), options.end(), "exitset") != options.end())
				annotater.annotateExitSet();
			if (std::find(options.begin(), options.end(), "entryset") != options.end())
				annotater.annotateEntrySet();
			if (std::find(options.begin(), options.end(), "domain") != options.end())
				annotater.annotateDomain();

			if (outputFile.size() == 0 || outputFile == "-") {
				std::cout << annotater.getDocument();
			} else {
				std::ofstream outStream;
				outStream.open(outputFile.c_str());
				outStream << annotater.getDocument();
				outStream.close();
			}
			exit(EXIT_SUCCESS);
		}
#endif


	} catch (Event e) {
		std::cout << e << std::endl;
	} catch (const std::exception &e) {
		std::cout << e.what() << std::endl;
	}

	return EXIT_SUCCESS;
}