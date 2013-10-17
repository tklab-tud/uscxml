/**
 *  @file
 *  @author     2012-2013 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#include "Sqlite3Invoker.h"
#include <glog/logging.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool pluginConnect(pluma::Host& host) {
	host.add( new Sqlite3InvokerProvider() );
	return true;
}
#endif

Sqlite3Invoker::Sqlite3Invoker() {
}

Sqlite3Invoker::~Sqlite3Invoker() {
};

boost::shared_ptr<InvokerImpl> Sqlite3Invoker::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<Sqlite3Invoker> invoker = boost::shared_ptr<Sqlite3Invoker>(new Sqlite3Invoker());
	invoker->_interpreter = interpreter;
	return invoker;
}

Data Sqlite3Invoker::getDataModelVariables() {
	Data data;
	return data;
}

void Sqlite3Invoker::send(const SendRequest& req) {
}

void Sqlite3Invoker::cancel(const std::string sendId) {
}

void Sqlite3Invoker::invoke(const InvokeRequest& req) {
}

}