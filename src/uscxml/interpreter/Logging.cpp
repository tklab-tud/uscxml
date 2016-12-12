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

#include "Logging.h"
#include "LoggingImpl.h"

// for default logger
#include "StdOutLogger.h"

namespace uscxml {

std::shared_ptr<LoggerImpl> LoggerImpl::_defaultLogger;

std::shared_ptr<LoggerImpl> LoggerImpl::getDefault() {
	if (!_defaultLogger)
		_defaultLogger = std::shared_ptr<LoggerImpl>(new StdOutLogger());
	return _defaultLogger;
}

Logger Logger::getDefault() {
	return LoggerImpl::getDefault();
}

void log(LogSeverity severity, const Event& event) {
	LoggerImpl::getDefault()->log(severity, event);
}

void log(LogSeverity severity, const Data& data) {
	LoggerImpl::getDefault()->log(severity, data);
}

void Logger::log(LogSeverity severity, const Event& event) {
	_impl->log(severity, event);
}

void Logger::log(LogSeverity severity, const Data& data) {
	_impl->log(severity, data);
}

void Logger::log(LogSeverity severity, const std::string& message) {
	_impl->log(severity, message);
}

StreamLogger Logger::log(LogSeverity severity) {
	return StreamLogger(severity, _impl);
}

StreamLogger::~StreamLogger() {
	_logger->log(_severity, ss.str());
}

std::shared_ptr<LoggerImpl> Logger::getImpl() const {
	return _impl;
}

std::ostream& StreamLogger::operator<<(const std::string& message) {
	ss << message; //_logger->log(_severity, event);
	return ss;
}

std::string Logger::severityToString(LogSeverity severity) {
	switch (severity) {
	case USCXML_SCXML:
		return "Interpreter";
	case USCXML_TRACE:
		return "Trace";
	case USCXML_DEBUG:
		return "Debug";
	case USCXML_INFO:
		return "Info";
	case USCXML_WARN:
		return "Warning";
	case USCXML_ERROR:
		return "Error";
	case USCXML_FATAL:
		return "Fatal";
	default:
		return "Unknown";

	}
}

}
