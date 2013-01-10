#include "HeartbeatInvoker.h"
#include <glog/logging.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool connect(pluma::Host& host) {
	host.add( new HeartbeatInvokerProvider() );
	return true;
}
#endif

HeartbeatInvoker::HeartbeatInvoker() {
}

HeartbeatInvoker::~HeartbeatInvoker() {
};

Invoker* HeartbeatInvoker::create(Interpreter* interpreter) {
	HeartbeatInvoker* invoker = new HeartbeatInvoker();
	invoker->_interpreter = interpreter;
	return invoker;
}

Data HeartbeatInvoker::getDataModelVariables() {
	Data data;
	return data;
}

void HeartbeatInvoker::send(SendRequest& req) {
}

void HeartbeatInvoker::cancel(const std::string sendId) {
  HeartbeatDispatcher::getInstance()->cancelEvent(toStr(this));
}

void HeartbeatInvoker::sendToParent(SendRequest& req) {
}

void HeartbeatInvoker::invoke(InvokeRequest& req) {
  _invokeId = req.invokeid;
  _event.invokeid = _invokeId;
  std::string intervalStr;
  double interval = 0;
  unsigned long intervalMs = 0;
  InvokeRequest::params_t::iterator paramIter = req.params.begin();
  while(paramIter != req.params.end()) {
    if (boost::iequals(paramIter->first, "interval")) {
      intervalStr = paramIter->second;
      NumAttr intervalAttr(paramIter->second);
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
      _event.name = paramIter->second;
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
  invoker->_interpreter->receive(invoker->_event);
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