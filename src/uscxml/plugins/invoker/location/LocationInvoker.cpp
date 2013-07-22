#include "LocationInvoker.h"
#include <glog/logging.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool connect(pluma::Host& host) {
	host.add( new LocationInvokerProvider() );
	return true;
}
#endif

LocationInvoker::LocationInvoker() {
}

LocationInvoker::~LocationInvoker() {
};

boost::shared_ptr<InvokerImpl> LocationInvoker::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<LocationInvoker> invoker = boost::shared_ptr<LocationInvoker>(new LocationInvoker());
	invoker->_interpreter = interpreter;
	return invoker;
}

Data LocationInvoker::getDataModelVariables() {
	Data data;
	return data;
}

void LocationInvoker::send(const SendRequest& req) {
}

void LocationInvoker::cancel(const std::string sendId) {
}

void LocationInvoker::invoke(const InvokeRequest& req) {
}

}