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

#ifndef HTTPSERVER_H_AIH108EG
#define HTTPSERVER_H_AIH108EG

#include <stddef.h>                     // for NULL

#include <map>                          // for map, map<>::iterator, etc
#include <string>                       // for string, operator<
#include <thread>
#include <mutex>

extern "C" {
#include "event2/util.h"                // for evutil_socket_t
#include <event2/http.h>                // for evhttp_request
#include <evws.h>
}

#include "uscxml/Common.h"              // for USCXML_API
#include "uscxml/messages/Event.h"      // for Data, Event
#include "uscxml/config.h"              // for OPENSSL_FOUND

namespace uscxml {

class HTTPServlet;
class WebSocketServlet;

class USCXML_API HTTPServer {
public:
	class Request : public Event {
	public:
		Request() : evhttpReq(NULL) {}
		std::string content;
		struct evhttp_request* evhttpReq;

		operator bool() {
			return evhttpReq != NULL;
		}
	};

	class USCXML_API SSLConfig {
	public:
		SSLConfig() : port(8443) {}
		std::string privateKey;
		std::string publicKey;
		unsigned short port;
	};

	class WSFrame : public Event {
	public:
		WSFrame() : evwsConn(NULL) {}
		std::string content;
		struct evws_connection* evwsConn;
	};

	class USCXML_API Reply {
	public:
		Reply() : status(200), type("get"), evhttpReq(NULL) {}
		Reply(Request req) : status(200), type(req.data.compound["type"].atom), evhttpReq(req.evhttpReq) {}

		void setRequest(Request req) {
			type = req.data.compound["type"].atom;
			evhttpReq = req.evhttpReq;
		}

		int status;
		std::string type;
		std::map<std::string, std::string> headers;
		std::string content;
		struct evhttp_request* evhttpReq;
	};

	struct CallbackData {
		HTTPServlet* servlet;
		evhttp_request* httpReq;
	};

	enum ServerType {
		HTTPS,
		HTTP,
		WebSockets
	};

	static HTTPServer* getInstance(unsigned short port, unsigned short wsPort, SSLConfig* sslConf = NULL);
	static HTTPServer* getInstance() {
		return getInstance(0, 0, NULL);
	}

	static std::string getBaseURL(ServerType type = HTTP);

	static void reply(const Reply& reply);
	static void wsSend(struct evws_connection *conn, enum evws_opcode opcode, const char *data, uint64_t length);
	static void wsBroadcast(const char *uri, enum evws_opcode opcode, const char *data, uint64_t length);

	static bool registerServlet(const std::string& path, HTTPServlet* servlet); ///< Register a servlet, returns false if path is already taken
	static void unregisterServlet(HTTPServlet* servlet);

	static bool registerServlet(const std::string& path, WebSocketServlet* servlet); ///< Register a servlet, returns false if path is already taken
	static void unregisterServlet(WebSocketServlet* servlet);

private:

	class WSData {
	public:
		WSData(struct evws_connection *conn_, const char *uri_, enum evws_opcode opcode_, const char *data_, uint64_t length_) {
			conn = conn_;
			if (uri_)
				uri = uri_;
			opcode = opcode_;
			data = std::string(data_, length_);
		}
		struct evws_connection *conn;
		std::string data;
		std::string uri;
		evws_opcode opcode;
	};

	struct comp_strsize_less {
		bool operator()(std::string const& l, std::string const& r) const {
			if (l.size() < r.size())
				return false;
			return true;
//			return l < r;
		};
	};

	HTTPServer(unsigned short port, unsigned short wsPort, SSLConfig* sslConf);
	virtual ~HTTPServer();

	void start();
	void stop();
	static void run(void* instance);

	void determineAddress();

	static void replyCallback(evutil_socket_t fd, short what, void *arg);
	static void wsSendCallback(evutil_socket_t fd, short what, void *arg);

	static void httpRecvReqCallback(struct evhttp_request *req, void *callbackData);
	static void wsRecvReqCallback(struct evws_connection *conn, struct evws_frame *, void *callbackData);

	void processByMatchingServlet(const Request& request);
	void processByMatchingServlet(evws_connection* conn, const WSFrame& frame);

	static std::map<std::string, std::string> mimeTypes;
	std::map<std::string, HTTPServlet*> _httpServlets;
	typedef std::map<std::string, HTTPServlet*>::iterator http_servlet_iter_t;

	std::map<std::string, WebSocketServlet*> _wsServlets;
	typedef std::map<std::string, WebSocketServlet*>::iterator ws_servlet_iter_t;

	struct event_base* _base;
	struct evhttp* _http;
	struct evws* _evws;

	struct evhttp_bound_socket* _httpHandle;
	evutil_socket_t _wsHandle;

	unsigned short _port;
	unsigned short _wsPort;
	std::string _address;

	static HTTPServer* _instance;

	static std::recursive_mutex _instanceMutex;
	std::thread* _thread;
	std::recursive_mutex _mutex;
	bool _isRunning;

	friend class HTTPServlet;
	friend class WebSocketServlet;

#if (defined EVENT_SSL_FOUND && defined OPENSSL_FOUND && defined OPENSSL_HAS_ELIPTIC_CURVES)
	struct evhttp* _https;
	struct evhttp_bound_socket* _sslHandle;
	unsigned short _sslPort;

	static struct bufferevent* sslBufferEventCallback(struct event_base *base, void *arg);
	static void sslGeneralBufferEventCallback (struct evhttp_request *req, void *arg);
#endif
};

class USCXML_API HTTPServlet {
public:
	virtual ~HTTPServlet() {}
	virtual bool requestFromHTTP(const HTTPServer::Request& request) = 0;
	virtual void setURL(const std::string& url) = 0; /// Called by the server with the actual URL
	virtual bool canAdaptPath() {
		return true;
	}
};

class USCXML_API WebSocketServlet {
public:
	virtual ~WebSocketServlet() {}
	virtual bool requestFromWS(struct evws_connection *conn, const HTTPServer::WSFrame& frame) = 0;
	virtual void setURL(const std::string& url) = 0; /// Called by the server with the actual URL
	virtual bool canAdaptPath() {
		return true;
	}
};

}

#endif /* end of include guard: HTTPSERVER_H_AIH108EG */
