#include "DelayedEventQueue.h"
#include <assert.h>
#include <event2/event.h>

namespace uscxml {

DelayedEventQueue::DelayedEventQueue() {
#ifndef _WIN32
	evthread_use_pthreads();
#else
	evthread_use_windows_threads();
#endif
	_eventLoop = event_base_new();
	_thread = NULL;
}

DelayedEventQueue::~DelayedEventQueue() {
//    std::cout << "Deleting DelayedEventQueue" << std::endl;
	stop();
	if (_thread)
		_thread->join();
	if(_eventLoop)
		event_base_free(_eventLoop);
}

void DelayedEventQueue::run(void* instance) {
	DelayedEventQueue* THIS = (DelayedEventQueue*)instance;
	int result;
	while(THIS->_isStarted) {
		{
			//result = event_base_dispatch(THIS->_eventLoop);
			result = event_base_loop(THIS->_eventLoop, EVLOOP_NO_EXIT_ON_EMPTY);
			(void)result;
		}
	}
}

void DelayedEventQueue::addEvent(std::string eventId, void (*callback)(void*, const std::string eventId), uint32_t delayMs, void* userData) {
	if(_callbackData.find(eventId) != _callbackData.end()) {
		cancelEvent(eventId);
	}

	struct timeval delay = {delayMs / 1000, (delayMs % 1000) * 1000};
	struct event* event = event_new(_eventLoop, -1, 0, DelayedEventQueue::timerCallback, &_callbackData[eventId]);

	_callbackData[eventId].eventId = eventId;
	_callbackData[eventId].userData = userData;
	_callbackData[eventId].eventQueue = this;
	_callbackData[eventId].callback = callback;
	_callbackData[eventId].event = event;

	event_add(event, &delay);
}

void DelayedEventQueue::cancelEvent(std::string eventId) {
	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);

	if(_callbackData.find(eventId) != _callbackData.end()) {
		event_del(_callbackData[eventId].event);
		event_free(_callbackData[eventId].event);
		_callbackData.erase(eventId);
	}
}

void DelayedEventQueue::start() {
	_isStarted = true;
	_thread = new tthread::thread(DelayedEventQueue::run, this);
}

void DelayedEventQueue::stop() {
	if (_isStarted) {
		_isStarted = false;
		event_base_loopbreak(_eventLoop);
		_thread->join();
		delete _thread;
	}
}

void DelayedEventQueue::dummyCallback(evutil_socket_t fd, short what, void *arg) {
}

void DelayedEventQueue::timerCallback(evutil_socket_t fd, short what, void *arg) {
	struct callbackData *data = (struct callbackData*)arg;
	tthread::lock_guard<tthread::recursive_mutex> lock(data->eventQueue->_mutex);

	std::string eventId = data->eventId; // copy eventId
	event_free(data->event);
	data->callback(data->userData, eventId);
	data->eventQueue->_callbackData.erase(data->eventId);
}

}