#ifndef DELAYEDEVENTQUEUE_H_JA6WRBVP
#define DELAYEDEVENTQUEUE_H_JA6WRBVP

#include "uscxml/concurrency/tinythread.h"

#include <event2/thread.h>
#include <event2/http.h>
#include <event2/event.h>

#include <inttypes.h>

#include <map>
#include <string>
#include <iostream>

namespace uscxml {

class DelayedEventQueue {
public:
	
  struct callbackData
  {
    void *userData;
    void (*callback)(void*, const std::string eventId);
    std::string eventId;
    struct event *event;
    DelayedEventQueue* eventQueue;
  };

	DelayedEventQueue();
	virtual ~DelayedEventQueue();
	
	void addEvent(std::string eventId, void (*callback)(void*, const std::string eventId), uint32_t delayMs, void* userData);
	void cancelEvent(std::string eventId);
	
	void start();
	void stop();
	static void run(void*);

  static void timerCallback(evutil_socket_t fd, short what, void *arg);
  static void dummyCallback(evutil_socket_t fd, short what, void *arg);

  bool _isStarted;
  tthread::thread* _thread;
  tthread::recursive_mutex _mutex;
  
  std::map<std::string, callbackData> _callbackData;
	struct event_base* _eventLoop;
};
	
}


#endif /* end of include guard: DELAYEDEVENTQUEUE_H_JA6WRBVP */
