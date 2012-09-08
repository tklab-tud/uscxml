#include "uscxml/concurrency/DelayedEventQueue.h"
#include <assert.h>

namespace uscxml {

  DelayedEventQueue::DelayedEventQueue() {
    _eventLoop = EV_DEFAULT;
    _thread = NULL;
  }

  DelayedEventQueue::~DelayedEventQueue() {
    ev_break(_eventLoop);
    if (_thread)
      _thread->join();
  }
	
	void DelayedEventQueue::addEvent(std::string eventId, void (*callback)(void*, const std::string eventId), uint32_t delayMs, void* userData) {
    if(_timeoutWatcher.find(eventId) != _timeoutWatcher.end()) {
      cancelEvent(eventId);
    }

    _timeoutWatcher[eventId].eventId = eventId;
    _timeoutWatcher[eventId].userData = userData;
    _timeoutWatcher[eventId].eventQueue = this;
    _timeoutWatcher[eventId].callback = callback;
    
    ev_timer_init (&_timeoutWatcher[eventId].io, DelayedEventQueue::timerCallback, ((float)delayMs)/1000.0f, 0.);
    ev_timer_start (_eventLoop, &_timeoutWatcher[eventId].io);

  }
	
  void DelayedEventQueue::cancelEvent(std::string eventId) {
    if(_timeoutWatcher.find(eventId) != _timeoutWatcher.end()) {
      ev_timer_stop(_eventLoop, &_timeoutWatcher[eventId].io);
      _timeoutWatcher.erase(eventId);
    }
  }
	
	void DelayedEventQueue::start() {
    _thread = new tthread::thread(DelayedEventQueue::run, this);
  }
  
	void DelayedEventQueue::stop() {
  }
  
	void DelayedEventQueue::run(void* instance) {
    ev_run (((DelayedEventQueue*)instance)->_eventLoop, 0);
  }
  
  void DelayedEventQueue::timerCallback(EV_P_ ev_timer *w, int revents) {
    struct callbackData *data = (struct callbackData*)w;
    std::string eventId = data->eventId; // copy eventId
    data->eventQueue->_timeoutWatcher.erase(data->eventId);
    data->callback(data->userData, eventId);
  }

}