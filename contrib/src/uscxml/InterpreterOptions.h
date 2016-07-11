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

#ifndef INTERPRETEROPTIONS_H_9D94370D
#define INTERPRETEROPTIONS_H_9D94370D

#include "uscxml/config.h"
#include "uscxml/Common.h"

#include <string>
#include <map>
#include <vector>

namespace uscxml {

/**
 * @ingroup interpreter
 * Options to pass into an interpreter.
 */
class USCXML_API InterpreterOptions {
public:
	InterpreterOptions() :
		verbose(false),
		validate(false),
		withHTTP(true),
		withHTTPS(true),
		withWS(true),
		withDebugger(false),
		logLevel(0),
		httpPort(5080),
		httpsPort(5443),
		wsPort(5081) {
	}

	bool verbose;
	bool validate;
	bool withHTTP;
	bool withHTTPS;
	bool withWS;
	bool withDebugger;
	int logLevel;
	unsigned short httpPort;
	unsigned short httpsPort;
	unsigned short wsPort;
	std::string pluginPath;
	std::string certificate;
	std::string privateKey;
	std::string publicKey;
	std::vector<std::pair<std::string, InterpreterOptions*> > interpreters;
	std::map<std::string, std::string> additionalParameters;

	std::string error;

	operator bool() {
		return error.length() == 0;
	}

	static void printUsageAndExit(const char* progName);
	static InterpreterOptions fromCmdLine(int argc, char** argv);

};

}

#endif /* end of include guard: INTERPRETEROPTIONS_H_9D94370D */
