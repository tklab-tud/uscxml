#include "uscxml/config.h"
#include "uscxml/Interpreter.h"
#include <glog/logging.h>

#ifdef _WIN32
#include "XGetopt.h"
#endif

void printUsageAndExit() {
	printf("mmi-browser version " USCXML_VERSION " (" CMAKE_BUILD_TYPE " build - " CMAKE_COMPILER_STRING ")\n");
	printf("Usage\n");
	printf("\tmmi-browser");
#ifdef BUILD_AS_PLUGINS
	printf(" [-p pluginPath]");
#endif
	printf(" URL\n");
	printf("\n");
	// printf("Options\n");
	// printf("\t-l loglevel       : loglevel to use\n");
	exit(1);
}

int main(int argc, char** argv) {
	using namespace uscxml;

	if (argc < 2) {
		printUsageAndExit();
	}

  opterr = 0;
	int option;
	while ((option = getopt(argc, argv, "l:p:")) != -1) {
		switch(option) {
		case 'l':
			google::InitGoogleLogging(optarg);
			break;
		case 'p':
			uscxml::Factory::pluginPath = optarg;
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
  

	Interpreter* interpreter = Interpreter::fromURI(argv[optind]);
	if (interpreter) {
    interpreter->setCmdLineOptions(argc, argv);
		interpreter->start();
		while(interpreter->runOnMainThread(25));
	}

	return EXIT_SUCCESS;
}