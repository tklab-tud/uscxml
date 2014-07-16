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

#include "EventBase.h"

namespace uscxml {

std::map<std::string, boost::weak_ptr<EventBase> > EventBase::_eventBases;
tthread::recursive_mutex EventBase::_instanceMutex;

boost::shared_ptr<EventBase> EventBase::get(const std::string& name) {
	tthread::lock_guard<tthread::recursive_mutex> lock(_instanceMutex);

	std::map<std::string, boost::weak_ptr<EventBase> >::iterator instIter = _eventBases.begin();
	while(instIter != _eventBases.end()) {
		if (!instIter->second.lock()) {
			_eventBases.erase(instIter++);
		} else {
			instIter++;
		}
	}

	instIter = _eventBases.find(name);
	boost::shared_ptr<EventBase> instance = instIter->second.lock();
	if (instance)
		return instance;

	instance = boost::shared_ptr<EventBase>(new EventBase());
	_eventBases.insert(std::make_pair(name, instance));

	return instance;
}

EventBase::EventBase() {
	base = event_base_new();
	_isStarted = true;
	_thread = new tthread::thread(EventBase::run, this);
}

void EventBase::run(void* arg) {
	EventBase* INSTANCE = (EventBase*)arg;
	int result;

	while(INSTANCE->_isStarted) {
		result = event_base_loop(INSTANCE->base, EVLOOP_NO_EXIT_ON_EMPTY);
		(void)result;
	}
}

EventBase::~EventBase() {
	_isStarted = false;
	event_base_loopbreak(base);
	_thread->join();
	event_base_free(base);
	delete _thread;
}

}