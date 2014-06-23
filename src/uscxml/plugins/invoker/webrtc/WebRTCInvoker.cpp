/**
 *  @file
 *  @author     2014 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#include "WebRTCInvoker.h"
#include <glog/logging.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

//#include "talk/app/webrtc/peerconnection.h"

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool pluginConnect(pluma::Host& host) {
	host.add( new WebRTCInvokerProvider() );
	return true;
}
#endif

WebRTCInvoker::WebRTCInvoker() {
}

WebRTCInvoker::~WebRTCInvoker() {
};

boost::shared_ptr<InvokerImpl> WebRTCInvoker::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<WebRTCInvoker> invoker = boost::shared_ptr<WebRTCInvoker>(new WebRTCInvoker());
	return invoker;
}

Data WebRTCInvoker::getDataModelVariables() {
	Data data;
	return data;
}

void WebRTCInvoker::send(const SendRequest& req) {
}

void WebRTCInvoker::cancel(const std::string sendId) {
}

void WebRTCInvoker::invoke(const InvokeRequest& req) {
}

}