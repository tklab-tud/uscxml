#include "USCXMLInvoker.h"
#include <glog/logging.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool connect(pluma::Host& host) {
	host.add( new USCXMLInvokerProvider() );
	return true;
}
#endif

USCXMLInvoker::USCXMLInvoker() {
}


USCXMLInvoker::~USCXMLInvoker() {
	delete _invokedInterpreter;
};

boost::shared_ptr<IOProcessorImpl> USCXMLInvoker::create(Interpreter* interpreter) {
	boost::shared_ptr<USCXMLInvoker> invoker = boost::shared_ptr<USCXMLInvoker>(new USCXMLInvoker());
	invoker->_parentInterpreter = interpreter;
	return invoker;
}

Data USCXMLInvoker::getDataModelVariables() {
	Data data;
	return data;
}

void USCXMLInvoker::send(const SendRequest& req) {
	assert(false);
}

void USCXMLInvoker::cancel(const std::string sendId) {
	assert(false);
}

void USCXMLInvoker::invoke(const InvokeRequest& req) {
	_invokedInterpreter = Interpreter::fromURI(req.src);
	DataModel dataModel(_invokedInterpreter->getDataModel());
	if (dataModel) {

	}
	if (_invokedInterpreter) {
		_invokedInterpreter->setParentQueue(this);
		_invokedInterpreter->start();
	}
}

void USCXMLInvoker::push(Event& event) {
	event.invokeid = _invokeId;
	_parentInterpreter->receive(event);
}

}