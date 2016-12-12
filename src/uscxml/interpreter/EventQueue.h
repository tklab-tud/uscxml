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

#ifndef EVENTQUEUE_H_C5C41BEE
#define EVENTQUEUE_H_C5C41BEE

#include "uscxml/Common.h"
#include "uscxml/messages/Event.h"

namespace uscxml {

class EventQueueImpl;
class DelayedEventQueueImpl;

/**
 * @ingroup eventqueue
 * @ingroup facade
 */
class USCXML_API EventQueue {
public:
	PIMPL_OPERATORS(EventQueue);

	virtual Event dequeue(size_t blockMs);
	virtual void enqueue(const Event& event);
	virtual void reset();
	virtual std::shared_ptr<EventQueueImpl> getImplBase();

protected:
	std::shared_ptr<EventQueueImpl> _impl;

};

/**
 * @ingroup eventqueue
 * @ingroup facade
 */
class USCXML_API DelayedEventQueue : public EventQueue {
public:
	PIMPL_OPERATORS_INHERIT(DelayedEventQueue, EventQueue);

	void enqueueDelayed(const Event& event, size_t delayMs, const std::string& eventUUID);
	void cancelDelayed(const std::string& eventUUID);
	void cancelAllDelayed();
	virtual std::shared_ptr<DelayedEventQueueImpl> getImplDelayed();

protected:
	std::shared_ptr<DelayedEventQueueImpl> _impl;
};

}

#endif /* end of include guard: EVENTQUEUE_H_C5C41BEE */
