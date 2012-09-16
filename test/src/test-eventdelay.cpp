#include "uscxml/concurrency/eventqueue/libevent/DelayedEventQueue.h"

int eventCalled = 0;

#include <sstream>

static void callback(void* userData, const std::string eventId) {
//  std::cout << eventId << ": " << (const char*)userData << std::endl;
  std::cout << eventId << std::endl << std::flush;
  eventCalled++;
}

int main(int argc, char** argv) {

  using namespace uscxml;
	DelayedEventQueue* eq = new DelayedEventQueue();

  std::cout << "Starting" << std::endl;
  eq->start();
  tthread::this_thread::sleep_for(tthread::chrono::milliseconds(10));

//  eq->addEvent("foo", callback, 200, (void*)"event foo");
//  eq->addEvent("bar", callback, 400, (void*)"event bar");
//  eq->addEvent("bar", callback, 600, (void*)"event bar");
//  eq->cancelEvent("bar");
//  eq->addEvent("bar", callback, 300, (void*)"event bar");
//  eq->addEvent("baz", callback, 400, (void*)"event baz");

  for (unsigned int i = 0; i <= 2000; i += 200) {
//    eq->stop();
    std::stringstream ss;
    ss << i;
    eq->addEvent(ss.str(), callback, i, NULL);
    std::cout << "Added " << i << std::endl;
//    eq->start();
  }
  tthread::this_thread::sleep_for(tthread::chrono::milliseconds(2000));

}