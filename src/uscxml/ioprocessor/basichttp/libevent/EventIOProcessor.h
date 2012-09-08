#ifndef EVENTIOPROCESSOR_H_2CUY93KU
#define EVENTIOPROCESSOR_H_2CUY93KU

#include "uscxml/concurrency/eventqueue/libevent/DelayedEventQueue.h"
#include "uscxml/Interpreter.h"
#include "uscxml/Factory.h"
#include <sys/time.h>

#include <event2/http.h>
#include <event2/http_struct.h>

namespace uscxml {
namespace io {
namespace libevent {

class EventIOServer;
  
class EventIOProcessor : public uscxml::IOProcessor {
public:
  struct SendData {
    EventIOProcessor* ioProcessor;
    uscxml::SendRequest req;
  };
  
  EventIOProcessor();
  virtual ~EventIOProcessor();
  virtual IOProcessor* create(uscxml::Interpreter* interpreter);

  virtual void send(uscxml::SendRequest& req);
  virtual void invoke(uscxml::InvokeRequest& req);
  virtual void cancel(const std::string sendId);

  std::string getURL() { return _url; }
  void setURL(const std::string& url) { _url = url; }
  
  void start();
  static void run(void* instance);

  static void httpMakeSendReq(void* userdata, std::string eventName);
  static void httpSendReqDone(struct evhttp_request *req, void *cb_arg);
  static void httpRecvReq(struct evhttp_request *req, void *arg);

protected:
  std::map<std::string, SendData> _sendData;
  
  std::string _url;
  
  uscxml::DelayedEventQueue _eventQueue;
  uscxml::Interpreter* _interpreter;
  std::map<std::string, struct evhttp_connection*> _httpConnections;
  std::map<std::string, struct evhttp_request*> _httpRequests;
  struct evdns_base* _dns;
  
  friend class EventIOServer;
};

class EventIOServer {
private:
  static EventIOServer* getInstance();
  EventIOServer(unsigned short port);
  ~EventIOServer();
  
  void start();
  void stop();
  static void run(void* instance);
  
  void determineAddress();
  static std::string syncResolve(const std::string& hostname);

  static void registerProcessor(EventIOProcessor* processor);
  static void unregisterProcessor(EventIOProcessor* processor);

  
  std::map<std::string, EventIOProcessor*> _processors;

  struct event_base* _base;
  struct evhttp* _http;
  struct evhttp_bound_socket* _handle;

  unsigned short _port;
  std::string _address;
  
  static EventIOServer* _instance;
  static tthread::recursive_mutex _instanceMutex;
  tthread::thread* _thread;
  tthread::recursive_mutex _mutex;
  bool _isRunning;
  
  friend class EventIOProcessor;
};

}
}
}

#endif /* end of include guard: EVENTIOPROCESSOR_H_2CUY93KU */