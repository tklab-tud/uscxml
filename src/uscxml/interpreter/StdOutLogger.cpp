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

#include "StdOutLogger.h"
#include <iostream>

namespace uscxml {

std::shared_ptr<LoggerImpl> StdOutLogger::create() {
	return std::shared_ptr<LoggerImpl>(new StdOutLogger());
}

void StdOutLogger::log(LogSeverity severity, const std::string& message) {
	std::cout << (severity != USCXML_VERBATIM ? Logger::severityToString(severity) + ": " : "") << message << std::flush;
}

void StdOutLogger::log(LogSeverity severity, const Event& event) {
	std::cout << (severity != USCXML_VERBATIM ? Logger::severityToString(severity) + ": " : "") << event << std::flush;
}

void StdOutLogger::log(LogSeverity severity, const Data& data) {
	std::cout << (severity != USCXML_VERBATIM ? Logger::severityToString(severity) + ": " : "") << data << std::flush;
}

}
