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

#ifndef EXECUTABLECONTENT_H_1E028A2D
#define EXECUTABLECONTENT_H_1E028A2D

#include "uscxml/Common.h"
#include <boost/shared_ptr.hpp>
#include <string>
#include <sstream>
#include "DOM/Document.hpp"

namespace uscxml {

class InterpreterImpl;

class USCXML_API ExecutableContentImpl {
public:
	ExecutableContentImpl() {};
	virtual ~ExecutableContentImpl() {};
	virtual boost::shared_ptr<ExecutableContentImpl> create(InterpreterImpl* interpreter) = 0;

	virtual void setInterpreter(InterpreterImpl* interpreter) {
		_interpreter = interpreter;
	}

	virtual std::string getLocalName() = 0; ///< The name of the element.
	virtual std::string getNamespace() {
		return "http://www.w3.org/2005/07/scxml";    ///< The namespace of the element.
	}
	virtual void enterElement(const Arabica::DOM::Element<std::string>& node) = 0; ///< Invoked when entering the element as part of evaluating executable content.
	virtual void exitElement(const Arabica::DOM::Element<std::string>& node) = 0; ///< Invoked when exiting the element as part of evaluating executable content.
	virtual bool processChildren() = 0; ///< Whether or not the interpreter should process this elements children.

protected:
	InterpreterImpl* _interpreter;
};

class USCXML_API ExecutableContent {
public:
	ExecutableContent() : _impl() {}
	ExecutableContent(boost::shared_ptr<ExecutableContentImpl> const impl) : _impl(impl) { }
	ExecutableContent(const ExecutableContent& other) : _impl(other._impl) { }
	virtual ~ExecutableContent() {};

	operator bool() const {
		return _impl;
	}
	bool operator< (const ExecutableContent& other) const     {
		return _impl < other._impl;
	}
	bool operator==(const ExecutableContent& other) const     {
		return _impl == other._impl;
	}
	bool operator!=(const ExecutableContent& other) const     {
		return _impl != other._impl;
	}
	ExecutableContent& operator= (const ExecutableContent& other)   {
		_impl = other._impl;
		return *this;
	}

	void setInterpreter(InterpreterImpl* interpreter) {
		_impl->setInterpreter(interpreter);
	}

	std::string getLocalName() {
		return _impl->getLocalName();
	}
	std::string getNamespace() {
		return _impl->getNamespace();
	}
	void enterElement(const Arabica::DOM::Element<std::string>& node) {
		return _impl->enterElement(node);
	}
	void exitElement(const Arabica::DOM::Element<std::string>& node) {
		return _impl->exitElement(node);
	}
	bool processChildren() {
		return _impl->processChildren();
	}
protected:
	boost::shared_ptr<ExecutableContentImpl> _impl;

};

}

#endif /* end of include guard: EXECUTABLECONTENT_H_1E028A2D */
