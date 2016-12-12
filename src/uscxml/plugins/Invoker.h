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

#ifndef INVOKER_H_CAC11892
#define INVOKER_H_CAC11892


#include "uscxml/Common.h"
#include "uscxml/plugins/EventHandler.h"
#include "uscxml/messages/Event.h"

namespace XERCESC_NS {
class DOMElement;
class DOMDocument;
class DOMNode;
}

namespace uscxml {

class InvokerImpl;

/**
 * @ingroup invoker
 * @ingroup facade
 * Facade for invoker implementation.
 */
class USCXML_API Invoker : public EventHandler {
public:
	PIMPL_OPERATORS_INHERIT(Invoker, EventHandler);

	/// @copydoc InvokerImpl::invoke
	virtual void invoke(const std::string& source, const Event& invokeEvent);

	/// @copydoc InvokerImpl::uninvoke
	virtual void uninvoke();

	/// @copydoc InvokerImpl::eventFromSCXML
	virtual void eventFromSCXML(const Event& event);

	/// @copydoc InvokerImpl::getFinalize
	virtual XERCESC_NS::DOMElement* getFinalize();

protected:
	std::shared_ptr<InvokerImpl> _impl;
};


}


#endif /* end of include guard: INVOKER_H_CAC11892 */
