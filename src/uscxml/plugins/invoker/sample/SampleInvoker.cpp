#include "SampleInvoker.h"
#include <glog/logging.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool connect(pluma::Host& host) {
	host.add( new SampleInvokerProvider() );
	return true;
}
#endif

SampleInvoker::SampleInvoker() {
}

SampleInvoker::~SampleInvoker() {
};

Invoker* SampleInvoker::create(Interpreter* interpreter) {
	SampleInvoker* invoker = new SampleInvoker();
	invoker->_interpreter = interpreter;
	return invoker;
}

Data SampleInvoker::getDataModelVariables() {
	Data data;
	return data;
}

void SampleInvoker::send(SendRequest& req) {
}

void SampleInvoker::cancel(const std::string sendId) {
}

void SampleInvoker::sendToParent(SendRequest& req) {
}

void SampleInvoker::invoke(InvokeRequest& req) {
  _invokeId = req.invokeid;
}

}