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

boost::shared_ptr<IOProcessorImpl> SampleInvoker::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<SampleInvoker> invoker = boost::shared_ptr<SampleInvoker>(new SampleInvoker());
	invoker->_interpreter = interpreter;
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