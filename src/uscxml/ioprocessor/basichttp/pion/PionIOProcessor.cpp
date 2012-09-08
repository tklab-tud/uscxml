#include "uscxml/ioprocessor/basichttp/pion/PionIOProcessor.h"
#include "uscxml/Message.h"

#include <pion/http/request.hpp>
#include <pion/http/message.hpp>

namespace uscxml {
  
using namespace pion;

PionIOProcessor::PionIOProcessor() {
}

PionIOProcessor::~PionIOProcessor() {
	
}

IOProcessor* PionIOProcessor::create(Interpreter* interpreter) {
  PionIOProcessor* io = new PionIOProcessor();
  io->_interpreter = interpreter;
  io->_ioServer = PionIOServer::getInstance();
  return io;
}

void handle_connection(pion::tcp::connection_ptr& tcp_conn) {
}

void PionIOProcessor::send(SendRequest& req) {

  boost::system::error_code error_code;
  boost::asio::io_service io_service;
  
  pion::tcp::connection tcp_conn(io_service, 0);
  error_code = tcp_conn.connect("localhost", 8080);
  if (error_code) throw error_code; // connection failed
  

  
  http::request httpReq;
  httpReq.set_method("POST");
  if (req.event.size() > 0)
    httpReq.add_header("_scxmleventname", req.event);

  httpReq.send(tcp_conn, error_code);
  
//  http::request_writer writer;
//  writer.

}
void PionIOProcessor::invoke(InvokeRequest& req) {
	
}
void PionIOProcessor::cancel(const std::string sendId) {
	
}

PionIOServer::PionIOServer() : pion::tcp::server(0) {
}

PionIOServer::~PionIOServer() {
}

void PionIOServer::handle_connection(pion::tcp::connection_ptr& tcp_conn) {
}

PionIOServer* PionIOServer::_instance = NULL;
PionIOServer* PionIOServer::getInstance() {
  if (_instance == NULL) {
    _instance = new PionIOServer();
  }
  return _instance;
}

}