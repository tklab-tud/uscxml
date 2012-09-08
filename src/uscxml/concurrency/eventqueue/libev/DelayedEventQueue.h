#ifndef DELAYEDEVENTQUEUE_H_JA6WRBVP
#define DELAYEDEVENTQUEUE_H_JA6WRBVP

#include "tinythread.h"
#include <ev.h>

#include <map>
#include <string>
#include <iostream>

namespace uscxml {

class DelayedEventQueue {
public:
	
  struct callbackData
  {
    ev_timer io;
    void *userData;
    void (*callback)(void*, const std::string eventId);
    std::string eventId;
    DelayedEventQueue* eventQueue;
  };

	DelayedEventQueue();
	virtual ~DelayedEventQueue();
	
	void addEvent(std::string eventId, void (*callback)(void*, const std::string eventId), uint32_t delayMs, void* userData);
	void cancelEvent(std::string eventId);
	
	void start();
	void stop();
	static void run(void*);

  static void timerCallback(EV_P_ ev_timer *w, int revents);

	tthread::thread* _thread;
  std::map<std::string, callbackData> _timeoutWatcher;
	struct ev_loop* _eventLoop;
};
	
}


#endif /* end of include guard: DELAYEDEVENTQUEUE_H_JA6WRBVP */
