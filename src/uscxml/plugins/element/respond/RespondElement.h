/**
 *  @file
 *  @author     2017 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#ifndef RESPONDELEMENT_H_564843
#define RESPONDELEMENT_H_564843

#include "uscxml/config.h"
#include "uscxml/interpreter/InterpreterImpl.h"
#include "uscxml/interpreter/BasicEventQueue.h"
#include "uscxml/interpreter/LoggingImpl.h"

#include "uscxml/plugins/ExecutableContentImpl.h"

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

/**
* @ingroup element
 * The respond element to reply to proper HTTP requests
 */
class USCXML_API RespondElement : public ExecutableContentImpl {
public:
	RespondElement() {};
	virtual ~RespondElement() {};

	virtual std::shared_ptr<ExecutableContentImpl> create(InterpreterImpl* interpreter) {
		std::shared_ptr<RespondElement> element(new RespondElement());
		element->_interpreter = interpreter;
		return element;
	}

	virtual std::string getLocalName() {
		return "respond";
	}
	virtual void enterElement(XERCESC_NS::DOMElement* node);
	virtual void exitElement(XERCESC_NS::DOMElement* node) {}

};

}
#endif /* end of include guard: RESPONDELEMENT_H_564843 */
