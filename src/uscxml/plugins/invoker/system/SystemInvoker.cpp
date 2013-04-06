#include "SystemInvoker.h"
#include <glog/logging.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool connect(pluma::Host& host) {
	host.add(new SystemInvokerProvider());
	return true;
}
#endif

SystemInvoker::SystemInvoker() {
}

SystemInvoker::~SystemInvoker() {
};

boost::shared_ptr<IOProcessorImpl> SystemInvoker::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<SystemInvoker> invoker = boost::shared_ptr<SystemInvoker>(new SystemInvoker());
	invoker->_interpreter = interpreter;
	return invoker;
}

Data SystemInvoker::getDataModelVariables() {
	Data data;
	return data;
}

void SystemInvoker::send(const SendRequest& req) {
}

void SystemInvoker::cancel(const std::string sendId) {
}

void SystemInvoker::invoke(const InvokeRequest& req) {
}

}