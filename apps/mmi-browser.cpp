#include "uscxml/config.h"
#include "uscxml/Interpreter.h"
#include <glog/logging.h>

#ifdef _WIN32
#include "XGetopt.h"
#endif

void printUsageAndExit() {
	printf("mmi-browser version " USCXML_VERSION " (" CMAKE_BUILD_TYPE " build)\n");
	printf("Usage\n");
	printf("\tmmi-browser URL\n");
	printf("\n");
	// printf("Options\n");
	// printf("\t-l loglevel       : loglevel to use\n");
	exit(1);
}

int main(int argc, char** argv) {
  if (argc < 2) {
		printUsageAndExit();
  }

	char* loglevel;
	int option;
	while ((option = getopt(argc, argv, "l:")) != -1) {
		switch(option) {
		case 'l':
			loglevel = optarg;
			break;
		default:
			printUsageAndExit();
			break;
		}
	}
  
	google::InitGoogleLogging(argv[0]);

  using namespace uscxml;

  Interpreter* interpreter = Interpreter::fromURI(argv[1]);
	interpreter->interpret();
	
  
	return EXIT_SUCCESS;
}