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

#ifndef IOPROCESSOR_H_CF4F4135
#define IOPROCESSOR_H_CF4F4135

#include "uscxml/Common.h"
#include "uscxml/plugins/EventHandler.h"

namespace uscxml {

class InterpreterImpl;

class USCXML_API IOProcessorImpl : public EventHandlerImpl {
public:
	IOProcessorImpl() {};
	virtual ~IOProcessorImpl() {};
	virtual boost::shared_ptr<IOProcessorImpl> create(InterpreterImpl* interpreter) = 0;
};

class USCXML_API IOProcessor : public EventHandler {
public:
	IOProcessor() : _impl() {}
	IOProcessor(boost::shared_ptr<IOProcessorImpl> const impl) : EventHandler(impl), _impl(impl) { }
	IOProcessor(const IOProcessor& other) : EventHandler(other._impl), _impl(other._impl) { }
	virtual ~IOProcessor() {};

	operator bool()                           const     {
		return !!_impl;
	}
	bool operator< (const IOProcessor& other) const     {
		return _impl < other._impl;
	}
	bool operator==(const IOProcessor& other) const     {
		return _impl == other._impl;
	}
	bool operator!=(const IOProcessor& other) const     {
		return _impl != other._impl;
	}
	IOProcessor& operator= (const IOProcessor& other)   {
		_impl = other._impl;
		EventHandler::_impl = _impl;
		return *this;
	}

protected:
	boost::shared_ptr<IOProcessorImpl> _impl;
	friend class InterpreterImpl;
};


}


#endif /* end of include guard: IOPROCESSOR_H_CF4F4135 */
