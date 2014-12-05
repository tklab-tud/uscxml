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
#include "uscxml/DOMUtils.h"

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
};

void USCXMLInvoker::uninvoke() {
	_cancelled = true;
	Event event;
	event.name = "unblock.and.die";
	if (_invokedInterpreter)
		_invokedInterpreter.receive(event);

}

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
	_cancelled = false;
	if (req.src.length() > 0) {
		_invokedInterpreter = Interpreter::fromURI(req.src);
	} else if (req.dom) {
		Arabica::DOM::DOMImplementation<std::string> domFactory = Arabica::SimpleDOM::DOMImplementation<std::string>::getDOMImplementation();
		Arabica::DOM::Document<std::string> dom = domFactory.createDocument(req.dom.getNamespaceURI(), "", 0);
		// we need to import the parent - to support xpath test150
		Arabica::DOM::Node<std::string> newNode = dom.importNode(req.dom, true);
		dom.appendChild(newNode);
		// TODO: where do we get the namespace from?
		_invokedInterpreter = Interpreter::fromDOM(dom, _interpreter->getNameSpaceInfo(), _interpreter->getSourceURI());
	} else if (req.content.size() > 0) {
		_invokedInterpreter = Interpreter::fromXML(req.content, _interpreter->getSourceURI());
	} else {
		LOG(ERROR) << "Cannot invoke nested SCXML interpreter, neither src attribute nor content nor DOM is given";
	}
	if (_invokedInterpreter) {
		if (req.elem && HAS_ATTR(req.elem, "initial")) {
			_invokedInterpreter.setInitalConfiguration(InterpreterImpl::tokenize(ATTR(req.elem, "initial")));
		}
		
		DataModel dataModel(_invokedInterpreter.getImpl()->getDataModel());
		_invokedInterpreter.getImpl()->setParentQueue(&_parentQueue);

		// transfer namespace prefixes
		_invokedInterpreter.setNameSpaceInfo(_parentInterpreter->getNameSpaceInfo());
		_invokedInterpreter.getImpl()->_sessionId = req.invokeid;

		/// test240 assumes that invoke request params will carry over to the datamodel
		_invokedInterpreter.getImpl()->setInvokeRequest(req);

		_invokedInterpreter.start();
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