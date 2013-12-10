/**
 *  @file
 *  @author     2012-2013 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#ifndef DELAYEDEVENTQUEUE_H_JA6WRBVP
#define DELAYEDEVENTQUEUE_H_JA6WRBVP

#include "uscxml/Common.h"
#include "uscxml/concurrency/tinythread.h"

#include <event2/thread.h>
#include <event2/http.h>
#include <event2/event.h>

#include <inttypes.h>

#include <map>
#include <string>
#include <iostream>

namespace uscxml {

class USCXML_API DelayedEventQueue {
public:

	enum OpMask {
	    DEQ_READ = EV_READ,
	    DEQ_WRITE = EV_WRITE,
	    DEQ_SIGNAL = EV_SIGNAL
	};

	struct callbackData {
		void *userData;
		void (*callback)(void*, const std::string eventId);
		std::string eventId;
		bool persist;
		struct event *event;
		DelayedEventQueue* eventQueue;
	};

	DelayedEventQueue();
	virtual ~DelayedEventQueue();

	void addEvent(std::string eventId, int fd, short opMask, void (*callback)(void*, const std::string eventId), void* userData, bool persist = true);
	void addEvent(std::string eventId, void (*callback)(void*, const std::string eventId), uint32_t delayMs, void* userData, bool persist = false);
	void cancelEvent(std::string eventId);

	void start();
	void stop();
	static void run(void*);

	bool isEmpty() {
		return _callbackData.empty();
	}

	static void timerCallback(evutil_socket_t fd, short what, void *arg);
	static void fileCallback(evutil_socket_t fd, short what, void *arg);
	static void dummyCallback(evutil_socket_t fd, short what, void *arg);

	bool _isStarted;
	tthread::thread* _thread;
	tthread::recursive_mutex _mutex;

	std::map<std::string, callbackData> _callbackData;
	struct event_base* _eventLoop;
};

}


#endif /* end of include guard: DELAYEDEVENTQUEUE_H_JA6WRBVP */
