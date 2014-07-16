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

#ifndef EVENTBASE_H_C479DA74
#define EVENTBASE_H_C479DA74

#include "uscxml/Common.h"
#include "uscxml/concurrency/tinythread.h"

extern "C" {
#include <event2/event.h>
#include <event2/buffer.h>
#include <event2/bufferevent.h>
}

#include <boost/shared_ptr.hpp>
#include <boost/weak_ptr.hpp>
#include <map>
#include <string>

namespace uscxml {

class USCXML_API EventBase {
public:
	EventBase();
	virtual ~EventBase();

	static boost::shared_ptr<EventBase> get(const std::string& name);
	struct event_base* base;

protected:

	static void run(void*);

	tthread::thread* _thread;
	bool _isStarted;

	static std::map<std::string, boost::weak_ptr<EventBase> > _eventBases;
	static tthread::recursive_mutex _instanceMutex;

};

}

#endif /* end of include guard: EVENTBASE_H_C479DA74 */
