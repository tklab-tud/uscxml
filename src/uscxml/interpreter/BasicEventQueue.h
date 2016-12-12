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

#ifndef BASICEVENTQUEUE_H_39DCC18B
#define BASICEVENTQUEUE_H_39DCC18B

#include "EventQueueImpl.h"
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
class USCXML_API BasicEventQueue : public EventQueueImpl {
public:
	BasicEventQueue();
	virtual ~BasicEventQueue();
	virtual std::shared_ptr<EventQueueImpl> create();
	virtual Event dequeue(size_t blockMs);
	virtual void enqueue(const Event& event);
	virtual void reset();

protected:
	std::list<Event> _queue;
	std::recursive_mutex _mutex;
	std::condition_variable_any _cond;
};

}

#endif /* end of include guard: BASICEVENTQUEUE_H_39DCC18B */
