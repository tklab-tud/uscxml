#ifndef PIONIOPROCESSOR_H_VAITDNCN
#define PIONIOPROCESSOR_H_VAITDNCN

#include "uscxml/Interpreter.h"
#include "uscxml/Factory.h"
#include "uscxml/concurrency/DelayedEventQueue.h"

#include <pion/http/request_writer.hpp>
#include <pion/http/request_writer.hpp>
#include <pion/tcp/server.hpp>

namespace uscxml {

class PionIOServer : public pion::tcp::server {
public:
  PionIOServer();
  virtual ~PionIOServer();
  DelayedEventQueue _eventQueue;
  
  virtual void handle_connection(pion::tcp::connection_ptr& tcp_conn);

  static PionIOServer* getInstance();
  static PionIOServer* _instance;
  
  pion::http::request_writer_ptr _writer;
  pion::tcp::connection_ptr _conn;

};

class PionIOProcessor : public IOProcessor {
public:
  PionIOProcessor();
  virtual ~PionIOProcessor();
  virtual IOProcessor* create(Interpreter* interpreter);

  virtual void send(SendRequest& req);
  virtual void invoke(InvokeRequest& req);
  virtual void cancel(const std::string sendId);

protected:
  Interpreter* _interpreter;
  PionIOServer* _ioServer;
};

}

#endif /* end of include guard: PIONIOPROCESSOR_H_VAITDNCN */
