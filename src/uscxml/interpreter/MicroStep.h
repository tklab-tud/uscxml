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

#ifndef MICROSTEP_H_07DA8BFA
#define MICROSTEP_H_07DA8BFA


#include <memory>
#include <list>
#include <string>

#include "uscxml/Common.h"
#include "uscxml/interpreter/InterpreterState.h"


// forward declare
namespace XERCESC_NS {
class DOMElement;
}

namespace uscxml {

class MicroStepImpl;

/**
 * @ingroup microstep
 * @ingroup facade
 */
class USCXML_API MicroStep {
public:
	PIMPL_OPERATORS(MicroStep);

	virtual InterpreterState step(size_t blockMs);
	virtual void reset();
	virtual bool isInState(const std::string& stateId);

	std::list<XERCESC_NS::DOMElement*> getConfiguration();

	virtual void init(XERCESC_NS::DOMElement* scxml);
	virtual void markAsCancelled();

	std::shared_ptr<MicroStepImpl> getImpl() const;
protected:
	std::shared_ptr<MicroStepImpl> _impl;
};

}

#endif /* end of include guard: MICROSTEP_H_07DA8BFA */
