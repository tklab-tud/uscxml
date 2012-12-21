#include "OSGInvoker.h"
#include <glog/logging.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool connect(pluma::Host& host) {
	host.add( new OSGInvokerProvider() );
	return true;
}
#endif

OSGInvoker::OSGInvoker() {
}

OSGInvoker::~OSGInvoker() {
};

Invoker* OSGInvoker::create(Interpreter* interpreter) {
	OSGInvoker* invoker = new OSGInvoker();
	invoker->_interpreter = interpreter;
	return invoker;
}

Data OSGInvoker::getDataModelVariables() {
	Data data;
	return data;
}

void OSGInvoker::send(SendRequest& req) {
}

void OSGInvoker::cancel(const std::string sendId) {
}

void OSGInvoker::sendToParent(SendRequest& req) {
}

void OSGInvoker::invoke(InvokeRequest& req) {
}

}