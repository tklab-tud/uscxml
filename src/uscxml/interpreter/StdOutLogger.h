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

#ifndef STDOUTLOGGER_H_1A28C761
#define STDOUTLOGGER_H_1A28C761

#include "LoggingImpl.h"

namespace uscxml {

class USCXML_API StdOutLogger : public LoggerImpl {
public:
	StdOutLogger() {}
	virtual ~StdOutLogger() {}

	virtual std::shared_ptr<LoggerImpl> create();

	virtual void log(LogSeverity severity, const std::string& message);
	virtual void log(LogSeverity severity, const Event& event);
	virtual void log(LogSeverity severity, const Data& data);

};


}

#endif /* end of include guard: STDOUTLOGGER_H_1A28C761 */
