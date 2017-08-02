/**
 *  @file
 *  @author     2016 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#ifndef CONTENTEXECUTOR_H_A2D592FA
#define CONTENTEXECUTOR_H_A2D592FA


#include "uscxml/Common.h"
#include "uscxml/messages/Data.h"
#include <string>

// forward declare
namespace XERCESC_NS {
class DOMElement;
}

namespace uscxml {

class ContentExecutorImpl;
class X;

/**
 * @ingroup execcontent
 * @ingroup facade
 */
class USCXML_API ContentExecutor {
public:
	PIMPL_OPERATORS(ContentExecutor);

	virtual void process(XERCESC_NS::DOMElement* block);
	virtual void invoke(XERCESC_NS::DOMElement* invoke);
	virtual void uninvoke(XERCESC_NS::DOMElement* invoke);
	virtual Data elementAsData(XERCESC_NS::DOMElement* element);
	virtual void raiseDoneEvent(XERCESC_NS::DOMElement* state, XERCESC_NS::DOMElement* doneData);
	virtual std::shared_ptr<ContentExecutorImpl> getImpl() const;

protected:
	std::shared_ptr<ContentExecutorImpl> _impl;
};

}

#endif /* end of include guard: CONTENTEXECUTOR_H_A2D592FA */
