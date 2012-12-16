#include "uscxml/config.h"
#include "uscxml/Interpreter.h"
#include <glog/logging.h>

#ifdef _WIN32
#include "XGetopt.h"
#endif

void printUsageAndExit() {
	printf("mmi-browser version " USCXML_VERSION " (" CMAKE_BUILD_TYPE " build - " CMAKE_COMPILER_STRING ")\n");
	printf("Usage\n");
	printf("\tmmi-browser [-p pluginPath] URL\n");
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

	char* loglevel = NULL;
	int option;
	while ((option = getopt(argc, argv, "l:p:")) != -1) {
		switch(option) {
		case 'l':
			loglevel = optarg;
			break;
    case 'p':
      uscxml::Factory::pluginPath = optarg;
      break;
		default:
			printUsageAndExit();
			break;
		}
	}
  
	Factory::getInstance();
	google::InitGoogleLogging(argv[0]);

  Interpreter* interpreter = Interpreter::fromURI(argv[1]);
	interpreter->interpret();
	
  
	return EXIT_SUCCESS;
}