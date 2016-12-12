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

#ifndef LOGGINGIMPL_H_CF00F49B
#define LOGGINGIMPL_H_CF00F49B

#include "uscxml/config.h"
#include "uscxml/Common.h"

#include "Logging.h"

#include "uscxml/messages/Data.h"
#include "uscxml/messages/Event.h"

namespace uscxml {

/**
* @ingroup impl
*/
class USCXML_API LoggerImpl {
public:

	LoggerImpl() {}
	virtual std::shared_ptr<LoggerImpl> create() = 0;

	virtual void log(LogSeverity severity, const Event& event) = 0;
	virtual void log(LogSeverity severity, const Data& data) = 0;
	virtual void log(LogSeverity severity, const std::string& message) = 0;

	static std::shared_ptr<LoggerImpl> getDefault();

private:
	static std::shared_ptr<LoggerImpl> _defaultLogger;
};

}

#endif /* end of include guard: LOGGINGIMPL_H_CF00F49B */
