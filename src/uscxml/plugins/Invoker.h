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

#ifndef INVOKER_H_CAC11892
#define INVOKER_H_CAC11892


#include "uscxml/Common.h"
#include "uscxml/plugins/EventHandler.h"
#include "uscxml/messages/Event.h"

namespace uscxml {

class Interpreter;

class USCXML_API InvokerImpl : public EventHandlerImpl {
public:
	InvokerImpl() : _finalize(NULL) {};
	virtual ~InvokerImpl() {}
	virtual std::list<std::string> getNames() = 0;

	virtual void invoke(const std::string& source, const Event& invokeEvent) = 0;
	virtual void uninvoke() = 0;

	virtual void eventFromSCXML(const Event& event) = 0;

	virtual std::shared_ptr<InvokerImpl> create(InterpreterImpl* interpreter) = 0;
	virtual xercesc::DOMElement* getFinalize() {
		return _finalize;
	}
	virtual void setFinalize(xercesc::DOMElement* finalize) {
		_finalize = finalize;
	}
	virtual void setInvokeId(const std::string& invokeId) {
		_invokeId = invokeId;
	}

protected:
	void eventToSCXML(Event& event, const std::string& type, const std::string& invokeId, bool internal = false);

	xercesc::DOMElement* _finalize;
	std::string _invokeId;

};

class USCXML_API Invoker : public EventHandler {
public:
	PIMPL_OPERATORS2(Invoker, EventHandler);

	virtual void invoke(const std::string& source, const Event& invokeEvent)     {
		_impl->invoke(source, invokeEvent);
	}

	virtual void uninvoke()     {
		_impl->uninvoke();
	}

	virtual void eventFromSCXML(const Event& event)     {
		_impl->eventFromSCXML(event);
	}

	virtual xercesc::DOMElement* getFinalize() {
		return _impl->getFinalize();
	}
protected:
	std::shared_ptr<InvokerImpl> _impl;
};


}


#endif /* end of include guard: INVOKER_H_CAC11892 */
