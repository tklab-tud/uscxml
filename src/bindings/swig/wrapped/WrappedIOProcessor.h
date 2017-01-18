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

#include <vector>
#include <list>
#include <ostream>
#include <string>

#include <xercesc/dom/DOM.hpp>

#include "../../../uscxml/messages/Event.h"
#include "../../../uscxml/plugins/Factory.h"
#include "../../../uscxml/plugins/IOProcessorImpl.h"
#include "../../../uscxml/Interpreter.h"

namespace uscxml {

class WrappedIOProcessor : public IOProcessorImpl {
public:
	WrappedIOProcessor(IOProcessorCallbacks* callbacks);
	virtual ~WrappedIOProcessor();

	virtual std::list<std::string> getNames() {
		return std::list<std::string>();
	};

	virtual std::shared_ptr<IOProcessorImpl> create(IOProcessorCallbacks* callbacks) {
		std::shared_ptr<IOProcessorImpl> ioProc = std::shared_ptr<IOProcessorImpl>(new WrappedIOProcessor(callbacks));
		return ioProc;
	}

	virtual void eventFromSCXML(const std::string& target, const Event& event) {}
	virtual bool isValidTarget(const std::string& target) {
		return true;
	}

	virtual Data getDataModelVariables() {
		return Data();
	}
};

}


#endif /* end of include guard: WRAPPEDIOPROCESSOR_H_AE98064A */
