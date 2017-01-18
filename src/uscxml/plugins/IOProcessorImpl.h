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

#ifndef IOPROCESSORIMPL_H_92E6AA44
#define IOPROCESSORIMPL_H_92E6AA44


#include "uscxml/Common.h"
#include "uscxml/plugins/EventHandler.h"
#include "uscxml/interpreter/Logging.h"
#include "uscxml/messages/Event.h"

namespace uscxml {

/**
 * @ingroup ioproc
 * @ingroup callback
 * Callbacks available for every IO processor.
 */
class USCXML_API IOProcessorCallbacks {
public:
	virtual ~IOProcessorCallbacks() {} ///< silence virtual destructor warning from swig
	virtual const std::string& getName() = 0;
	virtual const std::string& getSessionId() = 0;
	virtual void enqueueInternal(const Event& event) = 0;
	virtual void enqueueExternal(const Event& event) = 0;
	virtual void enqueueAtInvoker(const std::string& invokeId, const Event& event) = 0;
	virtual void enqueueAtParent(const Event& event) = 0;
	virtual Logger getLogger() = 0;

};

/**
 * @ingroup ioproc
 * @ingroup abstract
 * Abstract base class for IOProcessor%s implementations.
 */
class USCXML_API IOProcessorImpl : public EventHandlerImpl {
public:

	/**
	 * Factory demands a new instance.
	 * @param interpreter The imlementation of the associated Interpreter
	 * @todo We will eventually introduce callbacks and prevent complete access to the interpreter.
	 */
	virtual std::shared_ptr<IOProcessorImpl> create(IOProcessorCallbacks* callbacks) = 0;

	/**
	 * We received an event from the SCXML Interpreter we are associated with.
	 * @param target Where the event is supposed to be delivered to.
	 * @param event The event to deliver.
	 */
	virtual void eventFromSCXML(const std::string& target, const Event& event) = 0;

	/**
	 * Determine whether the given target is a valid destination for events.
	 * @param target A target where the Interpreter wants to deliver Event%s to.
	 * @return Whether or not the target is valid.
	 */
	virtual bool isValidTarget(const std::string& target) = 0;

protected:
	/**
	 * Return an event to the SCXML Interpreter instance.
	 * @param event An event to enqueue at the interpreter's external queue.
	 * @param type The type of this I/O Processor for `event.origintype`.
	 * @param origin The origin of this I/O Processor for `event.origin`.
	 * @param internal If the event is to be delivered to the Interpreter's internal queue instead.
	 */
	void eventToSCXML(Event& event, const std::string& type, const std::string& origin, bool internal = false);

	IOProcessorCallbacks* _callbacks;
};

}


#endif /* end of include guard: IOPROCESSORIMPL_H_92E6AA44 */
