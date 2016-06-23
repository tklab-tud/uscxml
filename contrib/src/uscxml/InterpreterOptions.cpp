/**
 *  @file
 *  @author     2016 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
 *  @copyright  Simplified BSD
 *
 *  @cond
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the FreeBSD license as published by the FreeBSD
 *  project.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 *
 *  You should have received a copy of the FreeBSD license along with this
 *  program. If not, see <http://www.opensource.org/licenses/bsd-license>.
 *  @endcond
 */

#include "uscxml/InterpreterOptions.h"
#include "uscxml/util/String.h"
#include "uscxml/util/Convenience.h"
#include "getopt.h"

#include <boost/algorithm/string.hpp>

#include <stdlib.h>

namespace uscxml {

void InterpreterOptions::printUsageAndExit(const char* progName) {

	// remove path from program name
	std::string progStr(progName);
	if (progStr.find_last_of(PATH_SEPERATOR) != std::string::npos) {
		progStr = progStr.substr(progStr.find_last_of(PATH_SEPERATOR) + 1, progStr.length() - (progStr.find_last_of(PATH_SEPERATOR) + 1));
	}

	printf("%s version " USCXML_VERSION " (" CMAKE_BUILD_TYPE " build - " CMAKE_COMPILER_STRING ")\n", progStr.c_str());
	printf("Usage\n");
	printf("\t%s", progStr.c_str());
	printf(" [-v] [-d] [-lN]");
#ifdef BUILD_AS_PLUGINS
	printf(" [-p pluginPath]");
#endif
	printf(" [-tN]");
#ifdef EVENT_SSL_FOUND
	printf(" [-sN] [--certificate=FILE | --private-key=FILE --public-key=FILE] ");
#endif
	printf(" \\\n\t\t URL1 [--disable-http] [--option1=value1 --option2=value2]");
	printf(" \\\n\t\t[URL2 [--disable-http] [--option3=value3 --option4=value4]]");
	printf(" \\\n\t\t[URLN [--disable-http] [--optionN=valueN --optionM=valueM]]");
	printf("\n");
	printf("Options\n");
#ifdef BUILD_AS_PLUGINS
	printf("\t-p        : path to the uSCXML plugins (or export USCXML_PLUGIN_PATH)\n");
#endif
	printf("\t-v        : be verbose\n");
    printf("\t-c        : perform some sanity checks on the state-chart\n");
	printf("\t-lN       : set loglevel to N\n");
	printf("\t-tN       : port for HTTP server\n");
	printf("\t-sN       : port for HTTPS server\n");
	printf("\t-wN       : port for WebSocket server\n");
    printf("\t-d        : start with debugger attachable\n");
	printf("\n");
    exit(1);
}

InterpreterOptions InterpreterOptions::fromCmdLine(int argc, char** argv) {
	InterpreterOptions options;
	optind = 0;
	struct option longOptions[] = {
		{"check",         no_argument,       0, 'c'},
		{"verbose",       no_argument,       0, 'v'},
		{"debug",         no_argument,       0, 'd'},
		{"port",          required_argument, 0, 't'},
		{"ssl-port",      required_argument, 0, 's'},
		{"ws-port",       required_argument, 0, 'w'},
		{"certificate",   required_argument, 0, 0},
		{"private-key",   required_argument, 0, 0},
		{"public-key",    required_argument, 0, 0},
		{"plugin-path",   required_argument, 0, 'p'},
		{"loglevel",      required_argument, 0, 'l'},
		{0, 0, 0, 0}
	};

	opterr = 0;
	InterpreterOptions* currOptions = &options;

	// parse global options
	int optionInd = 0;
	int option;
	for (;;) {
		option = getopt_long_only(argc, argv, "+vcdt:s:w:p:l:", longOptions, &optionInd);
		if (option == -1) {
			if (optind == argc)
				// we are done with parsing
				goto DONE_PARSING_CMD;

			std::string url = argv[optind];

			options.interpreters.push_back(std::make_pair(url, new InterpreterOptions()));
			currOptions = options.interpreters.back().second;

			argc -= optind;
			argv += optind;
			optind = 0;

			if (argc <= 1)
				goto DONE_PARSING_CMD;

		}
		switch(option) {
		// cases without short option
		case 0: {
			if (iequals(longOptions[optionInd].name, "disable-http")) {
				currOptions->withHTTP = false;
			} else if (iequals(longOptions[optionInd].name, "private-key")) {
				currOptions->privateKey = optarg;
			} else if (iequals(longOptions[optionInd].name, "certificate")) {
				currOptions->certificate = optarg;
			} else if (iequals(longOptions[optionInd].name, "public-key")) {
				currOptions->publicKey = optarg;
			}
			break;
		}
		// cases with short-hand options
		case 'l':
			currOptions->logLevel = strTo<unsigned int>(optarg);
			break;
		case 'p':
			currOptions->pluginPath = optarg;
			break;
		case 'c':
			currOptions->validate = true;
			break;
		case 'd':
			currOptions->withDebugger = true;
			break;
		case 't':
			currOptions->httpPort = strTo<unsigned short>(optarg);
			break;
		case 's':
			currOptions->httpsPort = strTo<unsigned short>(optarg);
			break;
		case 'w':
			currOptions->wsPort = strTo<unsigned short>(optarg);
			break;
		case 'v':
			currOptions->verbose = true;
			break;
		case '?': {
			std::string param = argv[optind - 1];
			if (boost::starts_with(param, "--")) {
				param = param.substr(2, param.length() - 2);
			}	else if (boost::starts_with(param, "-")) {
				param = param.substr(1, param.length() - 1);
			} else {
				break;
			}
			boost::trim(param);

			size_t equalPos = param.find("=");
			if (equalPos != std::string::npos) {
				std::string key = param.substr(0, equalPos);
				std::string value = param.substr(equalPos + 1, param.length() - (equalPos + 1));
				currOptions->additionalParameters[key] = value;
			} else {
				currOptions->additionalParameters[param] = "";
			}
			break;
		}
		default:
			break;
		}
	}

DONE_PARSING_CMD:

	if (options.interpreters.size() == 0 && !options.withDebugger)
		options.error = "No SCXML document to evaluate";

	return options;
}


}
