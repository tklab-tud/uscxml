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

#ifndef WRAPPEDIOPROCESSOR_H_AE98064A
#define WRAPPEDIOPROCESSOR_H_AE98064A

#include "../../../uscxml/Message.h"
#include "../../../uscxml/Factory.h"
#include "../../../uscxml/Interpreter.h"

namespace uscxml {

class WrappedIOProcessor : public IOProcessorImpl {
public:
	WrappedIOProcessor();
	virtual ~WrappedIOProcessor();

	virtual WrappedIOProcessor* create(const Interpreter& interpreter) {
		return new WrappedIOProcessor();
	}

	virtual boost::shared_ptr<IOProcessorImpl> create(InterpreterImpl* interpreter) {
		_interpreter = interpreter->shared_from_this();
		return boost::shared_ptr<IOProcessorImpl>(create(_interpreter));
	}
	virtual std::list<std::string> getNames() {
		return std::list<std::string>();
	};

	virtual Data getDataModelVariables() {
		Data data;
		return data;
	}
	
	virtual void send(const SendRequest& req) {
		
	}
	
private:
	Interpreter _interpreter;
};

}


#endif /* end of include guard: WRAPPEDIOPROCESSOR_H_AE98064A */
