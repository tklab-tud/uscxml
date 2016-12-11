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

#include "BasicEventQueue.h"
#include <event2/util.h>                // for evutil_socket_t
#include <event2/thread.h>
#include <assert.h>

#include "uscxml/interpreter/Logging.h"

namespace uscxml {

BasicEventQueue::BasicEventQueue() {
}
BasicEventQueue::~BasicEventQueue() {
}

Event BasicEventQueue::dequeue(size_t blockMs) {
	std::lock_guard<std::recursive_mutex> lock(_mutex);

	if (blockMs > 0) {

		// block for given milliseconds or until queue is filled
		auto endTime = std::chrono::system_clock::now() + std::chrono::milliseconds(blockMs);

		while (_queue.empty()) {
			_cond.wait_until(_mutex, endTime);
		}
	}

	if (_queue.size() > 0) {
		Event event = _queue.front();
		_queue.pop_front();
//        LOG(USCXML_ERROR) << event.name;
		return event;
	}
	return Event();

}

void BasicEventQueue::enqueue(const Event& event) {
	std::lock_guard<std::recursive_mutex> lock(_mutex);
	_queue.push_back(event);
	_cond.notify_all();
}

void BasicEventQueue::reset() {
	std::lock_guard<std::recursive_mutex> lock(_mutex);
	_queue.clear();
}

std::shared_ptr<EventQueueImpl> BasicEventQueue::create() {
    return std::shared_ptr<EventQueueImpl>(new BasicEventQueue());
}

}
