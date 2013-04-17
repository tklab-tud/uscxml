#include "MMIComponent.h"
//#include <glog/logging.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

MMIIOProcessor::MMIIOProcessor() {
}

MMIIOProcessor::~MMIIOProcessor() {
}

boost::shared_ptr<IOProcessorImpl> MMIIOProcessor::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<MMIIOProcessor> invoker = boost::shared_ptr<MMIIOProcessor>(new MMIIOProcessor());
	invoker->_interpreter = interpreter;
	return invoker;
}

Data MMIIOProcessor::getDataModelVariables() {
	Data data;
	return data;
}

void MMIIOProcessor::send(const SendRequest& req) {
}

}