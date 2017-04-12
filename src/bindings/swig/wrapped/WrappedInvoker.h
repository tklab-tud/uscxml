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

#include <xercesc/dom/DOM.hpp>

#include "../../../uscxml/messages/Event.h"
#include "../../../uscxml/plugins/Factory.h"
#include "../../../uscxml/plugins/InvokerImpl.h"

// forward declare
namespace XERCESC_NS {
class DOMElement;
}

namespace uscxml {

class WrappedInvoker : public InvokerImpl {
public:
	WrappedInvoker(InvokerCallbacks* callbacks);
	virtual ~WrappedInvoker();

	virtual std::list<std::string> getNames() {
		return std::list<std::string>();
	};

	virtual std::shared_ptr<InvokerImpl> create(InvokerCallbacks* callbacks) {
		std::shared_ptr<InvokerImpl> inv = std::shared_ptr<InvokerImpl>(new WrappedInvoker(callbacks));
		return inv;
	}
	virtual void invoke(const std::string& source, const Event& invokeEvent) {}
	virtual void uninvoke() {}

	virtual void eventFromSCXML(const Event& event) {}

	virtual void setInvokeId(const std::string& invokeId) {
		_invokeId = invokeId;
	}

	virtual Data getDataModelVariables() {
		return Data();
	}

	void eventToSCXML(Event& event, const std::string& type, const std::string& invokeId, bool internal = false) {

	}

private:
	InvokerCallbacks* _callbacks;

};

}

#endif /* end of include guard: WRAPPEDINVOKER_H_F9725D47 */
