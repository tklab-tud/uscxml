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

#ifndef CUSTOMEXECUTABLECONTENT_H_346FEA6
#define CUSTOMEXECUTABLECONTENT_H_346FEA6

#include <iostream>

#include "uscxml/plugins/ExecutableContentImpl.h"

class CustomExecutableContent : public uscxml::ExecutableContentImpl {
public:
	~CustomExecutableContent() {};
    virtual std::shared_ptr<ExecutableContentImpl> create(uscxml::InterpreterImpl* interpreter) {
        return std::shared_ptr<ExecutableContentImpl>(new CustomExecutableContent());
    }

	virtual std::string getLocalName() { return "custom"; }

	virtual void enterElement(XERCESC_NS::DOMElement* node) {
        std::cout << "Entering custom element" << std::endl;
	}
	virtual void exitElement(XERCESC_NS::DOMElement* node) {
		std::cout << "Exiting custom element" << std::endl;
	}

protected:
	uscxml::InterpreterImpl* _interpreter;
};


#endif /* end of include guard: CUSTOMEXECUTABLECONTENT_H_346FEA6 */
