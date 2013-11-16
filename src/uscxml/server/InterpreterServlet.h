/**
 *  @file
 *  @author     2012-2013 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#ifndef INTERPRETERSERVLET_H_XQLWNMH4
#define INTERPRETERSERVLET_H_XQLWNMH4

#include "HTTPServer.h"
#include "uscxml/Factory.h"

namespace uscxml {

class Interpreter;

class InterpreterHTTPServlet : public HTTPServlet, public IOProcessorImpl {
public:
	InterpreterHTTPServlet() {};
	InterpreterHTTPServlet(InterpreterImpl* interpreter);
	virtual ~InterpreterHTTPServlet() {}

	virtual boost::shared_ptr<IOProcessorImpl> create(InterpreterImpl* interpreter);

	virtual std::set<std::string> getNames() {
		std::set<std::string> names;
		names.insert("http");
		names.insert("http://www.w3.org/TR/scxml/#HTTPEventProcessor");
		return names;
	}

	Data getDataModelVariables();
	virtual void send(const SendRequest& req);

	virtual bool httpRecvRequest(const HTTPServer::Request& req);

	std::string getPath() {
		return _path;
	}
	std::string getURL() {
		return _url;
	}
	void setURL(const std::string& url) {
		_url = url;
	}
	bool canAdaptPath() {
		return false;
	}


	std::map<std::string, HTTPServer::Request>& getRequests() {
		return _requests;
	}
	tthread::recursive_mutex& getMutex() {
		return _mutex;
	}

protected:
	InterpreterImpl* _interpreter;

	tthread::recursive_mutex _mutex;
	std::map<std::string, HTTPServer::Request> _requests;
	std::string _path;
	std::string _url;

};

class InterpreterWebSocketServlet : public WebSocketServlet, public IOProcessorImpl {
public:
	InterpreterWebSocketServlet() {};
	InterpreterWebSocketServlet(InterpreterImpl* interpreter);
	virtual ~InterpreterWebSocketServlet() {}

	virtual boost::shared_ptr<IOProcessorImpl> create(InterpreterImpl* interpreter);

	virtual std::set<std::string> getNames() {
		std::set<std::string> names;
		names.insert("websocket");
		names.insert("http://www.w3.org/TR/scxml/#WebSocketEventProcessor");
		return names;
	}

	Data getDataModelVariables();
	virtual void send(const SendRequest& req);

	virtual bool wsRecvRequest(struct evws_connection *conn, const HTTPServer::WSFrame& frame);

	std::string getPath() {
		return _path;
	}
	std::string getURL() {
		return _url;
	}
	void setURL(const std::string& url) {
		_url = url;
	}
	bool canAdaptPath() {
		return false;
	}

	std::map<std::string, struct evws_connection*>& getRequests() {
		return _requests;
	}
	tthread::recursive_mutex& getMutex() {
		return _mutex;
	}

protected:
	InterpreterImpl* _interpreter;

	tthread::recursive_mutex _mutex;
	std::map<std::string, struct evws_connection*> _requests;
	std::string _path;
	std::string _url;

};

}


#endif /* end of include guard: INTERPRETERSERVLET_H_XQLWNMH4 */
