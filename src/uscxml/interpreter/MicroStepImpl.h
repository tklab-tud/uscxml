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

#ifndef MICROSTEPIMPL_H_98233709
#define MICROSTEPIMPL_H_98233709

#include <list>
#include <set>
#include <string>

#include "uscxml/Common.h"
#include "uscxml/Interpreter.h"
#include "uscxml/messages/Event.h"


namespace uscxml {

class InterpreterMonitor;

/**
 * @ingroup microstep
 * @ingroup callback
 */
class USCXML_API MicroStepCallbacks {
public:
	/** Event Queues / Matching */
	virtual Event dequeueInternal() = 0;
	virtual Event dequeueExternal(size_t blockMs) = 0;
	virtual bool isMatched(const Event& event, const std::string& eventDesc) = 0;
	virtual void raiseDoneEvent(XERCESC_NS::DOMElement* state, XERCESC_NS::DOMElement* doneData) = 0;

	/** Datamodel */
	virtual bool isTrue(const std::string& expr) = 0;
	virtual void initData(XERCESC_NS::DOMElement* element) = 0;

	/** Executable Content */
	virtual void process(XERCESC_NS::DOMElement* block) = 0;

	/** Invocations */
	virtual void invoke(XERCESC_NS::DOMElement* invoke) = 0;
	virtual void uninvoke(XERCESC_NS::DOMElement* invoke) = 0;

	/** Monitoring */
	virtual std::set<InterpreterMonitor*> getMonitors() = 0;
	virtual Interpreter getInterpreter() = 0;
	virtual Logger getLogger() = 0;
};

/**
 * @ingroup microstep
 * @ingroup impl
 */
class USCXML_API MicroStepImpl {
public:
	enum Binding {
		EARLY = 0,
		LATE = 1
	};

	MicroStepImpl(MicroStepCallbacks* callbacks) : _callbacks(callbacks) {}
	virtual std::shared_ptr<MicroStepImpl> create(MicroStepCallbacks* callbacks) = 0;

	virtual InterpreterState step(size_t blockMs) = 0;
	virtual void reset() = 0; ///< Reset state machine
	virtual bool isInState(const std::string& stateId) = 0;
	virtual std::list<XERCESC_NS::DOMElement*> getConfiguration() = 0;

	virtual void init(XERCESC_NS::DOMElement* scxml) = 0;
	virtual void markAsCancelled() = 0;

protected:
	MicroStepCallbacks* _callbacks;

};

}

#endif /* end of include guard: MICROSTEPIMPL_H_98233709 */
