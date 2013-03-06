#include "uscxml/config.h"
#include "uscxml/Interpreter.h"
#include <glog/logging.h>

#ifdef HAS_SIGNAL_H
#include <signal.h>
#endif

#ifdef _WIN32
#include "XGetopt.h"
#endif

#ifdef HAS_SIGNAL_H
void handler(int s) {
	printf("Caught SIGPIPE ############\n");
}
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

#ifdef HAS_SIGNAL_H
	// disable SIGPIPE
//  struct sigaction act;
//  act.sa_handler=SIG_IGN;
//  sigemptyset(&act.sa_mask);
//  act.sa_flags=0;
//  sigaction(SIGPIPE, &act, NULL);

	//  signal(SIGPIPE, handler);

	signal(SIGPIPE, SIG_IGN);

	//  struct sigaction act;
	//  int r;
	//  memset(&act, 0, sizeof(act));
	//  act.sa_handler = SIG_IGN;
	//  act.sa_flags = SA_RESTART;
	//  r = sigaction(SIGPIPE, &act, NULL);

#endif

	if (argc < 2) {
		printUsageAndExit();
	}

#ifndef _WIN32
	opterr = 0;
#endif
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
		//		interpreter->interpret();
		delete interpreter;
	}

	return EXIT_SUCCESS;
}