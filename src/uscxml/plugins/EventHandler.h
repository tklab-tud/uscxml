/**
 *  @file
 *  @author     2012-2014 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#ifndef EVENTHANDLER_H_2801243E
#define EVENTHANDLER_H_2801243E

#include "uscxml/Common.h"

#include <list>
#include <boost/shared_ptr.hpp>
#include <string>
#include <sstream>

#include "DOM/Document.hpp"
#include "uscxml/messages/SendRequest.h"

namespace uscxml {

class InterpreterImpl;

class USCXML_API EventHandlerImpl {
public:
	virtual ~EventHandlerImpl() {}

	virtual std::list<std::string> getNames() = 0;

	virtual void setInterpreter(InterpreterImpl* interpreter) {
		_interpreter = interpreter;
	}
	void setInvokeId(const std::string& invokeId) {
		_invokeId = invokeId;
	}
	void setType(const std::string& type) {
		_type = type;
	}

	void setElement(const Arabica::DOM::Element<std::string>& element) {
		_element = element;
	}

	Arabica::DOM::Element<std::string> getElement() {
		return _element;
	}

	virtual Data getDataModelVariables() = 0;
	virtual void send(const SendRequest& req) = 0;

	virtual void runOnMainThread() {};
	void returnEvent(Event& event);
	void returnErrorExecution(const std::string&);
	void returnErrorPlatform(const std::string&);

protected:
	InterpreterImpl* _interpreter;
	Arabica::DOM::Element<std::string> _element;
	std::string _invokeId;
	std::string _type;

};

class USCXML_API EventHandler {
public:
	EventHandler() : _impl() {}
	EventHandler(boost::shared_ptr<EventHandlerImpl> const impl) : _impl(impl) { }
	EventHandler(const EventHandler& other) : _impl(other._impl) { }
	virtual ~EventHandler() {};

	virtual std::list<std::string> getNames()   {
		return _impl->getNames();
	}

	virtual Data getDataModelVariables() const {
		return _impl->getDataModelVariables();
	};
	virtual void send(const SendRequest& req)  {
		return _impl->send(req);
	};
	virtual void runOnMainThread()             {
		return _impl->runOnMainThread();
	}

	void setInterpreter(InterpreterImpl* interpreter) {
		_impl->setInterpreter(interpreter);
	}
	void setInvokeId(const std::string& invokeId) {
		_impl->setInvokeId(invokeId);
	}
	void setType(const std::string& type) {
		_impl->setType(type);
	}

	void setElement(const Arabica::DOM::Element<std::string>& element) {
		_impl->setElement(element);
	}

	Arabica::DOM::Element<std::string> getElement() {
		return _impl->getElement();
	}

protected:
	boost::shared_ptr<EventHandlerImpl> _impl;
	friend class InterpreterImpl;
};


}


#endif /* end of include guard: EVENTHANDLER_H_2801243E */
