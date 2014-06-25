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

#ifndef WRAPPEDEXECUTABLECONTENT_H_F690F480
#define WRAPPEDEXECUTABLECONTENT_H_F690F480

#include "../../../uscxml/Message.h"
#include "../../../uscxml/Factory.h"
#include "../../../uscxml/Interpreter.h"

namespace uscxml {

class WrappedExecutableContent : public ExecutableContentImpl {
public:
	WrappedExecutableContent();
	virtual ~WrappedExecutableContent();

	virtual WrappedExecutableContent* create(const Interpreter& interpreter) {
		return new WrappedExecutableContent();
	}

	virtual boost::shared_ptr<ExecutableContentImpl> create(InterpreterImpl* interpreter) {
		_interpreter = interpreter->shared_from_this();
		return boost::shared_ptr<ExecutableContentImpl>(create(_interpreter));
	}
	
	virtual std::string getLocalName() {
		return "";
	}
	
	virtual std::string getNamespace() {
		return "http://www.w3.org/2005/07/scxml";
	}

	virtual void enterElement(const Arabica::DOM::Node<std::string>& node) {
		std::ostringstream ssElement;
		ssElement << node;
		enterElement(ssElement.str());
	}

	virtual void exitElement(const Arabica::DOM::Node<std::string>& node) {
		std::ostringstream ssElement;
		ssElement << node;
		exitElement(ssElement.str());		
	}

	virtual bool processChildren() {
		return false;
	}

	virtual void enterElement(const std::string& node) {
		
	}

	virtual void exitElement(const std::string& node) {
		
	}

	void croak() throw(Event) {
		
	}

private:
	Interpreter _interpreter;
};

}


#endif /* end of include guard: WRAPPEDEXECUTABLECONTENT_H_F690F480 */
