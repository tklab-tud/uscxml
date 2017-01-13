/**
 *  @file
 *  @author     2017 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#include "PausableDelayedEventQueue.h"
#include <assert.h>

namespace uscxml {

PausableDelayedEventQueue::PausableDelayedEventQueue(DelayedEventQueueCallbacks* callbacks) : BasicDelayedEventQueue(callbacks) {
	_pausedAt.tv_sec = 0;
	_pausedAt.tv_usec = 0;
}

std::shared_ptr<DelayedEventQueueImpl> PausableDelayedEventQueue::create(DelayedEventQueueCallbacks* callbacks) {
	return std::shared_ptr<PausableDelayedEventQueue>(new PausableDelayedEventQueue(callbacks));
}

void PausableDelayedEventQueue::pause() {
	if(_pausedAt.tv_sec != 0 || _pausedAt.tv_usec != 0) {
		return; // we are already paused!
	}

	evutil_gettimeofday(&_pausedAt, NULL); // remember when we paused

	{
		// Verbatim copy of stop() without cancelAllDelayed()
		if (_isStarted) {
			_isStarted = false;
			event_base_loopbreak(_eventLoop);
		}
		if (_thread) {
			_thread->join();
			delete _thread;
			_thread = NULL;
		}
	}

	std::lock_guard<std::recursive_mutex> lock(_mutex);

	// remove all events from libevent without deleting them
	for(auto callbackData : _callbackData) {
		Event data = callbackData.second.userData;
		event_del(callbackData.second.event);
	}
}

void PausableDelayedEventQueue::resume() {
	if (_pausedAt.tv_sec != 0 || _pausedAt.tv_usec != 0) {
		struct timeval now;
		struct timeval pausedFor;

		evutil_gettimeofday(&now, NULL);
		evutil_timersub(&now, &_pausedAt, &pausedFor);
		_pausedAt.tv_sec = 0;
		_pausedAt.tv_usec = 0;

		for(auto& callbackData : _callbackData) {
			// add the time we were paused to all due times
			evutil_timeradd(&callbackData.second.due, &pausedFor, &callbackData.second.due);

			struct timeval remain;
			evutil_timersub(&callbackData.second.due, &now, &remain);

#if 0
			std::cout << "Now      : " << now.tv_sec << "." << now.tv_usec << std::endl;
			std::cout << "Paused   : " << pausedFor.tv_sec << "." << pausedFor.tv_usec << std::endl;
			std::cout << "Remaining: " << remain.tv_sec << "." << remain.tv_usec << std::endl;
#endif
			assert(remain.tv_usec >= 0 && remain.tv_sec >= 0);

			// reenqueue with libevent
			event_add(callbackData.second.event, &remain);
		}
	}
	start();
}

}
