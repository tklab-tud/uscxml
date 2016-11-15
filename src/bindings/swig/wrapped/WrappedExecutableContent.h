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

#include <string>


#include "../../../uscxml/messages/Event.h"
#include "../../../uscxml/plugins/Factory.h"
#include "../../../uscxml/plugins/ExecutableContentImpl.h"

namespace uscxml {

class WrappedExecutableContent : public ExecutableContentImpl {
public:
	WrappedExecutableContent();
	virtual ~WrappedExecutableContent();

	virtual std::shared_ptr<ExecutableContentImpl> create(InterpreterImpl* interpreter) {
		std::shared_ptr<WrappedExecutableContent> ec(new WrappedExecutableContent());
		return ec;
	}

	virtual std::string getLocalName() {
		return "";
	}

	virtual std::string getNamespace() {
		return "http://www.w3.org/2005/07/scxml";
	}


	void enterElement(XERCESC_NS::DOMElement* element);
	virtual void enterElement(const std::string& elementXML) {}

	void exitElement(XERCESC_NS::DOMElement* element);
	virtual void exitElement(const std::string& elementXML) {}

	virtual bool processChildren() {
		return true;
	}

};

}


#endif /* end of include guard: WRAPPEDEXECUTABLECONTENT_H_F690F480 */
