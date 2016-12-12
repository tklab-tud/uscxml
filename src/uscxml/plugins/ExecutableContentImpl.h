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

#ifndef EXECUTABLECONTENTIMPL_H_CCE9F02D
#define EXECUTABLECONTENTIMPL_H_CCE9F02D

#include "uscxml/Common.h"

#include <string>
#include <memory>
#include <sstream>

namespace XERCESC_NS {
class DOMDocument;
class DOMNode;
}

namespace uscxml {

class InterpreterImpl;

/**
 * @ingroup element
 * @ingroup impl
 * Abstract base class fo all elements of executable content.
 */
class USCXML_API ExecutableContentImpl {
public:
	ExecutableContentImpl() {};
	virtual ~ExecutableContentImpl() {};
	virtual std::shared_ptr<ExecutableContentImpl> create(InterpreterImpl* interpreter) = 0;

	virtual void setInterpreter(InterpreterImpl* interpreter) {
		_interpreter = interpreter;
	}

	virtual std::string getLocalName() = 0; ///< The name of the element.
	virtual std::string getNamespace() {
		return "http://www.w3.org/2005/07/scxml";    ///< The namespace of the element.
	}
	virtual void enterElement(XERCESC_NS::DOMElement* node) = 0; ///< Invoked when entering the element as part of evaluating executable content.
	virtual void exitElement(XERCESC_NS::DOMElement* node) = 0; ///< Invoked when exiting the element as part of evaluating executable content.
	virtual bool processChildren() = 0; ///< Whether or not the interpreter should process this elements children.

protected:
	InterpreterImpl* _interpreter;
};


}

#endif /* end of include guard: EXECUTABLECONTENTIMPL_H_CCE9F02D */
