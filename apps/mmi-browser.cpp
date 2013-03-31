#include "uscxml/config.h"
#include "uscxml/Interpreter.h"
#include <glog/logging.h>

#ifdef HAS_SIGNAL_H
#include <signal.h>
#endif

#ifdef _WIN32
#include "XGetopt.h"
#endif

class VerboseMonitor : public uscxml::InterpreterMonitor {
	void onStableConfiguration(uscxml::Interpreter* interpreter) {
		printConfig(interpreter->getConfiguration());
	}

	void beforeCompletion(uscxml::Interpreter* interpreter) {
		printConfig(interpreter->getConfiguration());
	}

	void printConfig(const Arabica::XPath::NodeSet<std::string>& config) {
		std::string seperator;
		std::cout << "Config: {";
		for (int i = 0; i < config.size(); i++) {
			std::cout << seperator << ATTR(config[i], "id");
			seperator = ", ";
		}
		std::cout << "}" << std::endl;
	}
};

void printUsageAndExit() {
	printf("mmi-browser version " USCXML_VERSION " (" CMAKE_BUILD_TYPE " build - " CMAKE_COMPILER_STRING ")\n");
	printf("Usage\n");
	printf("\tmmi-browser");
#ifdef BUILD_AS_PLUGINS
	printf(" [-p pluginPath]");
#endif
	printf(" URL\n");
	printf("\n");
	printf("Options\n");
	printf("\t-v        : be verbose\n");
	printf("\n");
	exit(1);
}

int main(int argc, char** argv) {
	using namespace uscxml;

#ifdef HAS_SIGNAL_H
	signal(SIGPIPE, SIG_IGN);
#endif

	if (argc < 2) {
		printUsageAndExit();
	}

	bool verbose = false;
	google::InitGoogleLogging(argv[0]);
	google::LogToStderr();
	
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
			uscxml::Factory::pluginPath = optarg;
			break;
		case 'v':
			verbose = true;
			break;
		case '?':
			break;
		default:
			printUsageAndExit();
			break;
		}
	}

//  for (int i = 0; i < argc; i++)
//    std::cout << argv[i] << std::endl;
//  std::cout << optind << std::endl;

	LOG(INFO) << "Processing " << argv[optind];
	Interpreter* interpreter = Interpreter::fromURI(argv[optind]);
	if (interpreter) {
		interpreter->setCmdLineOptions(argc, argv);
//		interpreter->setCapabilities(Interpreter::CAN_NOTHING);
//		interpreter->setCapabilities(Interpreter::CAN_BASIC_HTTP | Interpreter::CAN_GENERIC_HTTP);

		if (verbose) {
			VerboseMonitor* vm = new VerboseMonitor();
			interpreter->addMonitor(vm);
		}

		interpreter->start();
		while(interpreter->runOnMainThread(25));
		delete interpreter;
	}

	return EXIT_SUCCESS;
}