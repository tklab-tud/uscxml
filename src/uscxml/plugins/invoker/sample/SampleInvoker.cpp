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

#include "SampleInvoker.h"
#include <glog/logging.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool pluginConnect(pluma::Host& host) {
	host.add( new SampleInvokerProvider() );
	return true;
}
#endif

SampleInvoker::SampleInvoker() {
}

SampleInvoker::~SampleInvoker() {
};

boost::shared_ptr<InvokerImpl> SampleInvoker::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<SampleInvoker> invoker = boost::shared_ptr<SampleInvoker>(new SampleInvoker());
	return invoker;
}

Data SampleInvoker::getDataModelVariables() {
	Data data;
	return data;
}

void SampleInvoker::send(const SendRequest& req) {
}

void SampleInvoker::cancel(const std::string sendId) {
}

void SampleInvoker::invoke(const InvokeRequest& req) {
}

}