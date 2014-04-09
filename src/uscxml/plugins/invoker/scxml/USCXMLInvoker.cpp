/**
 *  @file
 *  @author     2012-2013 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
 *  @copyright  Simplified BSD
 *
 *  @cond
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the FreeBSD license as published by the FreeBSD
 *  project.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 *
 *  You should have received a copy of the FreeBSD license along with this
 *  program. If not, see <http://www.opensource.org/licenses/bsd-license>.
 *  @endcond
 */

#include "USCXMLInvoker.h"
#include <glog/logging.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool pluginConnect(pluma::Host& host) {
	host.add( new USCXMLInvokerProvider() );
	return true;
}
#endif

USCXMLInvoker::USCXMLInvoker() : _cancelled(false) {
	_parentQueue._invoker = this;
}


USCXMLInvoker::~USCXMLInvoker() {
	_cancelled = true;
};

boost::shared_ptr<InvokerImpl> USCXMLInvoker::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<USCXMLInvoker> invoker = boost::shared_ptr<USCXMLInvoker>(new USCXMLInvoker());
	invoker->_parentInterpreter = interpreter;
	return invoker;
}

Data USCXMLInvoker::getDataModelVariables() {
	Data data;
	return data;
}

void USCXMLInvoker::send(const SendRequest& req) {
	_invokedInterpreter.receive(req);
}

void USCXMLInvoker::cancel(const std::string sendId) {
	assert(false);
}

void USCXMLInvoker::invoke(const InvokeRequest& req) {
	if (req.src.length() > 0) {
		_invokedInterpreter = Interpreter::fromURI(req.src);
	} else if (req.dom) {
		Arabica::DOM::DOMImplementation<std::string> domFactory = Arabica::SimpleDOM::DOMImplementation<std::string>::getDOMImplementation();
		Arabica::DOM::Document<std::string> dom = domFactory.createDocument(req.dom.getNamespaceURI(), "", 0);
		// we need to import the parent - to support xpath test150
		Arabica::DOM::Node<std::string> newNode = dom.importNode(req.dom, true);
		dom.appendChild(newNode);
		// TODO: where do we get the namespace from?
		_invokedInterpreter = Interpreter::fromDOM(dom, std::map<std::string, std::string>());
	} else if (req.content.size() > 0) {
		_invokedInterpreter = Interpreter::fromXML(req.content);
	} else {
		LOG(ERROR) << "Cannot invoke nested SCXML interpreter, neither src attribute nor content nor DOM is given";
	}
	if (_invokedInterpreter) {
		DataModel dataModel(_invokedInterpreter.getImpl()->getDataModel());
		_invokedInterpreter.getImpl()->setParentQueue(&_parentQueue);
		// transfer namespace prefixes
		_invokedInterpreter.getImpl()->_nsURL = _parentInterpreter->_nsURL;
		_invokedInterpreter.getImpl()->_xpathPrefix = _parentInterpreter->_xpathPrefix;
		_invokedInterpreter.getImpl()->_nsToPrefix = _parentInterpreter->_nsToPrefix;
		std::map<std::string, std::string>::iterator nsIter =  _parentInterpreter->_nsToPrefix.begin();
		while(nsIter != _parentInterpreter->_nsToPrefix.end()) {
			_invokedInterpreter.getImpl()->_nsContext.addNamespaceDeclaration(nsIter->first, nsIter->second);
			nsIter++;
		}
		_invokedInterpreter.getImpl()->_xmlNSPrefix = _parentInterpreter->_xmlNSPrefix;
		_invokedInterpreter.getImpl()->_sessionId = req.invokeid;

		/// test240 assumes that invoke request params will carry over to the datamodel
		_invokedInterpreter.getImpl()->setInvokeRequest(req);

		_invokedInterpreter.start();
//		tthread::this_thread::sleep_for(tthread::chrono::seconds(1));
	} else {
		/// test 530
		_parentInterpreter->receive(Event("done.invoke." + _invokeId, Event::PLATFORM));
	}
}

void USCXMLInvoker::ParentQueue::push(const SendRequest& event) {
	// test 252
	if (_invoker->_cancelled)
		return;
	SendRequest copyEvent(event);
	copyEvent.invokeid = _invoker->_invokeId;
	_invoker->_parentInterpreter->receive(copyEvent);
}

}