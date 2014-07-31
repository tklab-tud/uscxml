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

#ifndef WRAPPEDINVOKER_H_F9725D47
#define WRAPPEDINVOKER_H_F9725D47

#include <vector>
#include <list>
#include <ostream>
#include <string>

#include <DOM/Document.hpp>
#include <DOM/io/Stream.hpp>

#include "../../../uscxml/Message.h"
#include "../../../uscxml/Factory.h"
#include "../../../uscxml/Interpreter.h"

namespace uscxml {

class WrappedInvoker : public InvokerImpl {
public:
	WrappedInvoker();
	virtual ~WrappedInvoker();

	virtual std::list<std::string> getNames() {
		return std::list<std::string>();
	};

	virtual Data getDataModelVariables() {
		Data data;
		return data;
	}

	virtual void send(const SendRequest& req) {}
	virtual void invoke(const InvokeRequest& req) {}
	virtual void uninvoke() {}

	virtual bool deleteOnUninvoke() {
		return false;
	}

	virtual WrappedInvoker* create(const Interpreter& interpreter) {
		return new WrappedInvoker();
	}

	virtual boost::shared_ptr<InvokerImpl> create(InterpreterImpl* interpreter) {
		_interpreter = interpreter->shared_from_this();
		return boost::shared_ptr<InvokerImpl>(create(_interpreter));
	}

private:
	Interpreter _interpreter;

};

}

#endif /* end of include guard: WRAPPEDINVOKER_H_F9725D47 */
