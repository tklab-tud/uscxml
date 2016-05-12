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

#ifndef EVENTSOURCE_H_775AB206
#define EVENTSOURCE_H_775AB206

#include "uscxml/Common.h"
#include "uscxml/messages/Event.h"
#include <string>
#include <map>
#include <list>
#include <thread>
#include <mutex>
#include <condition_variable>

#include <event2/event.h>


namespace uscxml {

class USCXML_API EventQueueImpl {
public:
	EventQueueImpl();
	virtual ~EventQueueImpl();
	virtual Event dequeue(bool blocking);
	virtual void enqueue(const Event& event);

protected:
	std::list<Event> _queue;
	std::recursive_mutex _mutex;
	std::condition_variable_any _cond;

};

class USCXML_API DelayedEventQueueCallbacks {
public:
	virtual void eventReady(Event& event, const std::string& eventId) = 0;
};

class USCXML_API DelayedEventQueueImpl : public EventQueueImpl {
public:
	DelayedEventQueueImpl(DelayedEventQueueCallbacks* callbacks);
	virtual ~DelayedEventQueueImpl();
	virtual void enqueueDelayed(const Event& event, size_t delayMs, const std::string& eventUUID);
	virtual void cancelDelayed(const std::string& eventId);
	virtual void cancelAllDelayed();

protected:
	struct callbackData {
		Event userData;
		std::string eventUUID;
		bool persist;
		struct event *event;
		DelayedEventQueueImpl* eventQueue;
	};

	bool _isStarted;
	std::thread* _thread;

	std::map<std::string, callbackData> _callbackData;
	struct event_base* _eventLoop;
	struct event* _dummyEvent;

	static void run(void* instance);
	void start();
	void stop();

	static void timerCallback(evutil_socket_t fd, short what, void *arg);
	DelayedEventQueueCallbacks* _callbacks;
};

class USCXML_API EventQueue {
public:
	PIMPL_OPERATORS(EventQueue)

	virtual Event dequeue(bool blocking) {
		return _impl->dequeue(blocking);
	}
	virtual void enqueue(const Event& event) {
		return _impl->enqueue(event);
	}

protected:
	std::shared_ptr<EventQueueImpl> _impl;

};

class USCXML_API DelayedEventQueue : public EventQueue {
public:
	PIMPL_OPERATORS2(DelayedEventQueue, EventQueue)

	void enqueueDelayed(const Event& event, size_t delayMs, const std::string& eventUUID) {
		_impl->enqueueDelayed(event, delayMs, eventUUID);
	}
	void cancelDelayed(const std::string& eventUUID) {
		return _impl->cancelDelayed(eventUUID);
	}

	void cancelAllDelayed() {
		return _impl->cancelAllDelayed();
	}

protected:
	std::shared_ptr<DelayedEventQueueImpl> _impl;
};

}

#endif /* end of include guard: EVENTSOURCE_H_775AB206 */
