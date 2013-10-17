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

#include "HeartbeatInvoker.h"
#include <glog/logging.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool pluginConnect(pluma::Host& host) {
	host.add( new HeartbeatInvokerProvider() );
	return true;
}
#endif

HeartbeatInvoker::HeartbeatInvoker() {
}

HeartbeatInvoker::~HeartbeatInvoker() {
	cancel("");
};

boost::shared_ptr<InvokerImpl> HeartbeatInvoker::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<HeartbeatInvoker> invoker = boost::shared_ptr<HeartbeatInvoker>(new HeartbeatInvoker());
	invoker->_interpreter = interpreter;
	return invoker;
}

Data HeartbeatInvoker::getDataModelVariables() {
	Data data;
	return data;
}

void HeartbeatInvoker::send(const SendRequest& req) {
}

void HeartbeatInvoker::cancel(const std::string sendId) {
	HeartbeatDispatcher::getInstance()->cancelEvent(toStr(this));
}

void HeartbeatInvoker::invoke(const InvokeRequest& req) {
	_invokeId = req.invokeid;
	_event.invokeid = _invokeId;
	std::string intervalStr;
	double interval = 0;
	unsigned long intervalMs = 0;
	InvokeRequest::params_t::const_iterator paramIter = req.params.begin();
	while(paramIter != req.params.end()) {
		if (boost::iequals(paramIter->first, "interval")) {
			intervalStr = paramIter->second.atom;
			NumAttr intervalAttr(paramIter->second.atom);
			interval = strTo<double>(intervalAttr.value);
			if (false) {
			} else if (boost::iequals(intervalAttr.unit, "s")) {
				intervalMs = interval * 1000;
			} else if (boost::iequals(intervalAttr.unit, "ms")) {
				intervalMs = interval;
			} else {
				intervalMs = interval;
			}
		}
		if (boost::iequals(paramIter->first, "eventname")) {
			_event.name = paramIter->second.atom;
		}
		paramIter++;
	}
	if (_event.name.length() == 0)
		_event.name = std::string("heartbeat." + intervalStr);

	if (intervalMs > 0) {
		HeartbeatDispatcher::getInstance()->addEvent(toStr(this), HeartbeatInvoker::dispatch, intervalMs, this, true);
	}
}

void HeartbeatInvoker::dispatch(void* instance, std::string name) {
	HeartbeatInvoker* invoker = (HeartbeatInvoker*)instance;
	invoker->returnEvent(invoker->_event);
}

HeartbeatDispatcher* HeartbeatDispatcher::_instance = NULL;
HeartbeatDispatcher* HeartbeatDispatcher::getInstance() {
	if (_instance == NULL) {
		_instance = new HeartbeatDispatcher();
		_instance->start();
	}
	return _instance;
}

HeartbeatDispatcher::HeartbeatDispatcher() {}

}