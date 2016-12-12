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

#ifndef EVENTQUEUEIMPL_H_48027643
#define EVENTQUEUEIMPL_H_48027643

#include "uscxml/Common.h"
#include "uscxml/messages/Event.h"
#include <string>
#include <map>
#include <list>
#include <thread>
#include <mutex>
#include <condition_variable>


namespace uscxml {

/**
 * @ingroup eventqueue
 * @ingroup impl
 */
class USCXML_API EventQueueImpl {
public:
	virtual std::shared_ptr<EventQueueImpl> create() = 0;
	virtual Event dequeue(size_t blockMs) = 0;
	virtual void enqueue(const Event& event) = 0;
	virtual void reset() = 0;
};

/**
 * @ingroup eventqueue
 * @ingroup callback
 */
class USCXML_API DelayedEventQueueCallbacks {
public:
	virtual void eventReady(Event& event, const std::string& eventId) = 0;
};

/**
 * @ingroup eventqueue
 * @ingroup impl
 */
class USCXML_API DelayedEventQueueImpl : public EventQueueImpl {
public:
	virtual std::shared_ptr<DelayedEventQueueImpl> create(DelayedEventQueueCallbacks*) = 0;
	virtual void enqueueDelayed(const Event& event, size_t delayMs, const std::string& eventUUID) = 0;
	virtual void cancelDelayed(const std::string& eventId) = 0;
	virtual void cancelAllDelayed() = 0;
};

}

#endif /* end of include guard: EVENTQUEUEIMPL_H_48027643 */
