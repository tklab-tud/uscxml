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
#include "uscxml/messages/InvokeRequest.h"

namespace uscxml {

class InterpreterImpl;

class USCXML_API InvokerImpl : public EventHandlerImpl {
public:
	virtual ~InvokerImpl() {}
	virtual void invoke(const InvokeRequest& req) = 0;
	virtual void uninvoke() {}

	virtual bool deleteOnUninvoke() {
		return true;
	}

	virtual boost::shared_ptr<InvokerImpl> create(InterpreterImpl* interpreter) = 0;
};

class USCXML_API Invoker : public EventHandler {
public:
	Invoker() : _impl() {}
	Invoker(boost::shared_ptr<InvokerImpl> const impl) : EventHandler(impl), _impl(impl) { }
	Invoker(const Invoker& other) : EventHandler(other._impl), _impl(other._impl) { }
	virtual ~Invoker() {};

	operator bool()                       const {
		return _impl;
	}
	bool operator< (const Invoker& other) const {
		return _impl < other._impl;
	}
	bool operator==(const Invoker& other) const {
		return _impl == other._impl;
	}
	bool operator!=(const Invoker& other) const {
		return _impl != other._impl;
	}
	Invoker& operator= (const Invoker& other)   {
		_impl = other._impl;
		EventHandler::_impl = _impl;
		return *this;
	}

	virtual void invoke(InvokeRequest& req)     {
		_impl->invoke(req);
	}

	virtual void uninvoke()     {
		_impl->uninvoke();
	}

	virtual bool deleteOnUninvoke() {
		return _impl->deleteOnUninvoke();
	}

protected:
	boost::shared_ptr<InvokerImpl> _impl;
};


}


#endif /* end of include guard: INVOKER_H_CAC11892 */
