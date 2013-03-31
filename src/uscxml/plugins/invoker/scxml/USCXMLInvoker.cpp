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
	if (req.src.length() > 0) {
		_invokedInterpreter = Interpreter::fromURI(req.src);
	} else if (req.dom) {
		_invokedInterpreter = Interpreter::fromDOM(req.dom);
	} else {
		LOG(ERROR) << "Cannot invoke nested SCXML interpreter, neither src attribute nor DOM is given";
	}
	DataModel dataModel(_invokedInterpreter->getDataModel());
	if (dataModel) {

	}
	if (_invokedInterpreter) {
		_invokedInterpreter->setParentQueue(this);
		// transfer namespace prefixes
		_invokedInterpreter->_nsURL = _parentInterpreter->_nsURL;
		_invokedInterpreter->_xpathPrefix = _parentInterpreter->_xpathPrefix;
		_invokedInterpreter->_nsToPrefix = _parentInterpreter->_nsToPrefix;
		std::map<std::string, std::string>::iterator nsIter =  _parentInterpreter->_nsToPrefix.begin();
		while(nsIter != _parentInterpreter->_nsToPrefix.end()) {
			_invokedInterpreter->_nsContext.addNamespaceDeclaration(nsIter->first, nsIter->second);
			nsIter++;
		}
		_invokedInterpreter->_xmlNSPrefix = _parentInterpreter->_xmlNSPrefix;
		_invokedInterpreter->start();
	}
}

void USCXMLInvoker::push(const SendRequest& event) {
	SendRequest copyEvent(event);
	copyEvent.invokeid = _invokeId;
	_parentInterpreter->receive(copyEvent);
}

}