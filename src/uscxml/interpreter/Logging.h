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

#ifndef LOGGING_H_3B1A3A0F
#define LOGGING_H_3B1A3A0F

#include "uscxml/Common.h"
#include "uscxml/messages/Data.h"
#include "uscxml/messages/Event.h"

#include <memory>

#define LOG(logger, lvl) logger.log(lvl)
#define LOG2(logger, lvl, thing) logger.log(lvl, thing)
#define LOGD(lvl) uscxml::Logger::getDefault().log(lvl)
#define LOGD2(lvl, thing) uscxml::Logger::getDefault().log(lvl, thing);

namespace uscxml {

enum LogSeverity {
	USCXML_SCXML,
	USCXML_TRACE,
	USCXML_DEBUG,
	USCXML_INFO,
	USCXML_WARN,
	USCXML_ERROR,
	USCXML_FATAL
};

class LoggerImpl;

void log(LogSeverity severity, const Event& event);
void log(LogSeverity severity, const Data& data);

class StreamLogger {
public:
	std::ostream& operator<<(const std::string& message);
	~StreamLogger();

protected:
	StreamLogger(LogSeverity severity, std::shared_ptr<LoggerImpl> logger) : _severity(severity), _logger(logger) {}
	StreamLogger(const StreamLogger& other) : _severity(other._severity), _logger(other._logger) {}

	LogSeverity _severity;
	std::shared_ptr<LoggerImpl> _logger;
	std::stringstream ss;

	friend class Logger;
};

class USCXML_API Logger {
public:
	PIMPL_OPERATORS(Logger);

	virtual void log(LogSeverity severity, const Event& event);
	virtual void log(LogSeverity severity, const Data& data);
	virtual void log(LogSeverity severity, const std::string& message);

	virtual StreamLogger log(LogSeverity severity);
	static std::string severityToString(LogSeverity severity);

	static Logger getDefault();

	std::shared_ptr<LoggerImpl> getImpl() const;
protected:
	std::shared_ptr<LoggerImpl> _impl;

};

}

#endif /* end of include guard: LOGGING_H_3B1A3A0F */
