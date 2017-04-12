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

#ifndef INVOKERIMPL_H_8A15A102
#define INVOKERIMPL_H_8A15A102


#include "uscxml/config.h"
#include "uscxml/Common.h"
#include "uscxml/plugins/EventHandler.h"
#include "uscxml/messages/Event.h"

#include <set>

namespace uscxml {

class Interpreter;
class InterpreterMonitor;
class ActionLanguage;
class Logger;

/**
 * @ingroup invoker
 * @ingroup callback
 * Callbacks available for every invoker.
 */
class USCXML_API InvokerCallbacks {
public:
	virtual ~InvokerCallbacks() {} ///< silence virtual destructor warning from swig
	virtual void enqueueInternal(const Event& event) = 0;
	virtual void enqueueExternal(const Event& event) = 0;
	virtual ActionLanguage* getActionLanguage() = 0; /// We return a pointer to relax dependencies in transpiled mode
	virtual std::set<InterpreterMonitor*> getMonitors() = 0;
	virtual std::string getBaseURL() = 0;
	virtual Logger getLogger() = 0;
};

/**
 * @ingroup invoker
 * @ingroup abstract
 * Abstract base class for all invokers.
 */
class USCXML_API InvokerImpl : public EventHandlerImpl {
public:
	InvokerImpl() {};
	virtual ~InvokerImpl() {}

	virtual std::list<std::string> getNames() = 0;

	/**
	 * Factory demands a new instance.
	 * @param callbacks An object implementing the invoker callbacks.
	 */
	virtual std::shared_ptr<InvokerImpl> create(InvokerCallbacks* callbacks) = 0;

	/**
	 * Invoker's parent state became active at the end of a macro-step.
	 * @param source The content of the invoke's `src` or evaluated `srcexpr` attribute
	 * @param invokeEvent The invocation with all its data as an event
	 */
	virtual void invoke(const std::string& source, const Event& invokeEvent) = 0;

	/**
	 * The invokers's parent state was left at the end of a macro-step.
	 */
	virtual void uninvoke() = 0;

	/**
	 * Invoker received an event from the SCXML Interpreter.
	 */
	virtual void eventFromSCXML(const Event& event) = 0;

	/**
	 * Set the invocation identifier as required when returning events.
	 * @param invokeId The invocation identifier.
	 */
	virtual void setInvokeId(const std::string& invokeId) {
		_invokeId = invokeId;
	}

	/**
	 * Load a state from a Data object
	 * @param encodedState The state we returned somewhen else via serialize.
	 */
	virtual void deserialize(const Data& encodedState) {}

	/**
	 * Save our state into a Data object
	 */
	virtual Data serialize() {
		return Data();
	}

protected:
	/**
	 * Return an event to the SCXML Interpreter instance.
	 * @param event An event to enqueue at the interpreter's external queue.
	 * @param type The type of this I/O Processor for `event.origintype`.
	 * @param invokeId The invocation identifier of this invocation for `event.invokeid`.
	 * @param internal If the event is to be delivered to the Interpreter's internal queue instead.
	 */
	void eventToSCXML(Event& event, const std::string& type, const std::string& invokeId, bool internal = false);

	std::string _invokeId;
	InvokerCallbacks* _callbacks;
};

}


#endif /* end of include guard: INVOKERIMPL_H_8A15A102 */
