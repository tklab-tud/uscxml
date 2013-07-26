#include "CalendarInvoker.h"
#include <glog/logging.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool connect(pluma::Host& host) {
	host.add( new CalendarInvokerProvider() );
	return true;
}
#endif

CalendarInvoker::CalendarInvoker() {
}

CalendarInvoker::~CalendarInvoker() {
};

boost::shared_ptr<InvokerImpl> CalendarInvoker::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<CalendarInvoker> invoker = boost::shared_ptr<CalendarInvoker>(new CalendarInvoker());
	invoker->_interpreter = interpreter;
	return invoker;
}

Data CalendarInvoker::getDataModelVariables() {
	Data data;
	return data;
}

void CalendarInvoker::send(const SendRequest& req) {
}

void CalendarInvoker::cancel(const std::string sendId) {
}

void CalendarInvoker::invoke(const InvokeRequest& req) {
}

}