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

#include <memory>
#include <mutex>
#include <list>
#include <map>
#include <string>

#include "uscxml/Common.h"
#include "uscxml/messages/Event.h"
#include "uscxml/interpreter/InterpreterMonitor.h"
#include "uscxml/util/DOM.h"
#include <xercesc/dom/DOM.hpp>

namespace uscxml {

enum InterpreterState {


	USCXML_FINISHED       = -2,  ///< machine reached a final configuration and is done
	USCXML_INTERRUPTED    = -1,  ///< machine received the empty event on the external queue
	USCXML_UNDEF          = 0,   ///< not an actual state
	USCXML_IDLE           = 1,   ///< stable configuration and queues empty
	USCXML_INITIALIZED    = 2,   ///< DOM is setup and all external components instantiated
	USCXML_INSTANTIATED   = 3,   ///< nothing really, just instantiated
	USCXML_MICROSTEPPED   = 4,   ///< processed one transition set
	USCXML_MACROSTEPPED   = 5,   ///< processed all transition sets and reached a stable configuration
	USCXML_CANCELLED      = 6,   ///< machine was cancelled, step once more to finalize
};

class USCXML_API MicroStepCallbacks {
public:
	/** Event Queues / Matching */
	virtual Event dequeueInternal() = 0;
	virtual Event dequeueExternal(bool blocking) = 0;
	virtual bool isMatched(const Event& event, const std::string& eventDesc) = 0;
	virtual void raiseDoneEvent(xercesc::DOMElement* state, xercesc::DOMElement* doneData) = 0;

	/** Datamodel */
	virtual bool isTrue(const std::string& expr) = 0;
	virtual void initData(xercesc::DOMElement* element) = 0;

	/** Executable Content */
	virtual void process(xercesc::DOMElement* block) = 0;

	/** Invocations */
	virtual void invoke(xercesc::DOMElement* invoke) = 0;
	virtual void uninvoke(xercesc::DOMElement* invoke) = 0;

	/** Monitoring */
	virtual InterpreterMonitor* getMonitor() = 0;
};

class USCXML_API MicroStepImpl {
public:
	enum Binding {
		EARLY = 0,
		LATE = 1
	};

	MicroStepImpl(MicroStepCallbacks* callbacks) : _callbacks(callbacks) {}

	virtual InterpreterState step(bool blocking) = 0;
	virtual void reset() = 0; ///< Reset state machine
	virtual bool isInState(const std::string& stateId) = 0;
	virtual std::list<xercesc::DOMElement*> getConfiguration() = 0;

	virtual void init(xercesc::DOMElement* scxml) = 0;
	virtual void markAsCancelled() = 0;

protected:
	MicroStepCallbacks* _callbacks;

};

class USCXML_API MicroStep {
public:
	PIMPL_OPERATORS(MicroStep)

	virtual InterpreterState step(bool blocking) {
		return _impl->step(blocking);
	}
	virtual void reset() {
		return _impl->reset();
	}
	virtual bool isInState(const std::string& stateId) {
		return _impl->isInState(stateId);
	}

	std::list<xercesc::DOMElement*> getConfiguration() {
		return _impl->getConfiguration();
	}

	virtual void init(xercesc::DOMElement* scxml) {
		_impl->init(scxml);
	}

	virtual void markAsCancelled() {
		_impl->markAsCancelled();
	}
protected:
	std::shared_ptr<MicroStepImpl> _impl;
};

}

#endif /* end of include guard: MICROSTEPIMPL_H_98233709 */
