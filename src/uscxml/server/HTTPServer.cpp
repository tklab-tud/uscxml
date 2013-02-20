#ifdef _WIN32
#include <winsock2.h>
#include <windows.h>
#endif

#include "uscxml/server/HTTPServer.h"
#include "uscxml/Message.h"
#include <iostream>
#include <event2/dns.h>
#include <event2/event.h>
#include <event2/buffer.h>
#include <event2/http.h>
#include <event2/keyvalq_struct.h>
#include <event2/http_struct.h>
#include <event2/thread.h>

#include <string.h>

#include <glog/logging.h>
#include <boost/algorithm/string.hpp>

#ifndef _WIN32
#include <netdb.h>
#include <arpa/inet.h>
#endif

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

HTTPServer::HTTPServer(unsigned short port) {
	_port = port;
	_base = event_base_new();
	_http = evhttp_new(_base);
	_handle = NULL;
	while((_handle = evhttp_bind_socket_with_handle(_http, INADDR_ANY, _port)) == NULL) {
		_port++;
	}
	determineAddress();
}

HTTPServer::~HTTPServer() {
}

HTTPServer* HTTPServer::_instance = NULL;
tthread::recursive_mutex HTTPServer::_instanceMutex;

HTTPServer* HTTPServer::getInstance(int port) {
	tthread::lock_guard<tthread::recursive_mutex> lock(_instanceMutex);
	if (_instance == NULL) {
#ifndef _WIN32
		evthread_use_pthreads();
#else
		evthread_use_windows_threads();
#endif
		_instance = new HTTPServer(port);
		_instance->start();
	}
	return _instance;
}

void HTTPServer::httpRecvReqCallback(struct evhttp_request *req, void *callbackData) {
//  std::cout << (uintptr_t)req << ": Replying" << std::endl;
//  evhttp_send_reply(req, 200, NULL, NULL);
//  return;

	Request request;
	request.curlReq = req;

	switch (evhttp_request_get_command(req)) {
	case EVHTTP_REQ_GET:
		request.type = "GET";
		break;
	case EVHTTP_REQ_POST:
		request.type = "POST";
		break;
	case EVHTTP_REQ_HEAD:
		request.type = "HEAD";
		break;
	case EVHTTP_REQ_PUT:
		request.type = "PUT";
		break;
	case EVHTTP_REQ_DELETE:
		request.type = "DELETE";
		break;
	case EVHTTP_REQ_OPTIONS:
		request.type = "OPTIONS";
		break;
	case EVHTTP_REQ_TRACE:
		request.type = "TRACE";
		break;
	case EVHTTP_REQ_CONNECT:
		request.type = "CONNECT";
		break;
	case EVHTTP_REQ_PATCH:
		request.type = "PATCH";
		break;
	default:
		request.type = "unknown";
		break;
	}

	struct evkeyvalq *headers;
	struct evkeyval *header;
	struct evbuffer *buf;

	// map headers to event structure
	headers = evhttp_request_get_input_headers(req);
	for (header = headers->tqh_first; header; header = header->next.tqe_next) {
		request.headers[header->key] = header->value;
	}

	request.remoteHost = req->remote_host;
	request.remotePort = req->remote_port;
	request.httpMajor = req->major;
	request.httpMinor = req->minor;
	request.uri = req->uri;

	// get content
	buf = evhttp_request_get_input_buffer(req);
	while (evbuffer_get_length(buf)) {
		int n;
		char cbuf[1024];
		n = evbuffer_remove(buf, cbuf, sizeof(buf)-1);
		if (n > 0) {
			request.content.append(cbuf, n);
		}
	}

	((HTTPServlet*)callbackData)->httpRecvRequest(request);
}

void HTTPServer::reply(const Reply& reply) {
	struct evbuffer *evb = evbuffer_new();

	std::map<std::string, std::string>::const_iterator headerIter = reply.headers.begin();
	while(headerIter != reply.headers.end()) {
		evhttp_add_header(evhttp_request_get_output_headers(reply.curlReq), headerIter->first.c_str(), headerIter->second.c_str());
		headerIter++;
	}

	if (!boost::iequals(reply.type, "HEAD"))
		evbuffer_add(evb, reply.content.data(), reply.content.size());

	evhttp_send_reply(reply.curlReq, reply.status, NULL, evb);
	evbuffer_free(evb);
//  evhttp_request_free(reply.curlReq);

}

bool HTTPServer::registerServlet(const std::string& path, HTTPServlet* servlet) {
	HTTPServer* INSTANCE = getInstance();
	tthread::lock_guard<tthread::recursive_mutex> lock(INSTANCE->_mutex);

	/**
	 * Determine path for interpreter.
	 *
	 * If the interpreter has a name and it is not yet taken, choose it as the path
	 * for requests. If the interpreters name path is already taken, append digits
	 * until we have an available path.
	 *
	 * If the interpreter does not specify a name, take its sessionid.
	*
	* Responsibility moved to individual servlets.
	 */

	if(INSTANCE->_servlets.find(path) != INSTANCE->_servlets.end()) {
		return false;
	}

	std::stringstream servletURL;
	servletURL << "http://" << INSTANCE->_address << ":" << INSTANCE->_port << "/" << path;
	servlet->setURL(servletURL.str());

	INSTANCE->_servlets[path] = servlet;

	LOG(INFO) << "HTTP Servlet listening at: " << servletURL.str() << std::endl;

	// register callback
	evhttp_set_cb(INSTANCE->_http, ("/" + path).c_str(), HTTPServer::httpRecvReqCallback, servlet);

	return true;
	// generic callback
//  evhttp_set_cb(THIS->_http, "/", EventIOProcessor::httpRecvReq, processor);
//  evhttp_set_gencb(THIS->_http, EventIOProcessor::httpRecvReq, NULL);
}

void HTTPServer::unregisterServlet(HTTPServlet* servlet) {
	HTTPServer* INSTANCE = getInstance();
	tthread::lock_guard<tthread::recursive_mutex> lock(INSTANCE->_mutex);
	servlet_iter_t servletIter = INSTANCE->_servlets.begin();
	while(servletIter != INSTANCE->_servlets.end()) {
		if (servletIter->second == servlet) {
			evhttp_del_cb(INSTANCE->_http, std::string("/" + servletIter->first).c_str());
			INSTANCE->_servlets.erase(servletIter);
			break;
		}
		servletIter++;
	}
}

void HTTPServer::start() {
	_isRunning = true;
	_thread = new tthread::thread(HTTPServer::run, this);
}

void HTTPServer::run(void* instance) {
	HTTPServer* INSTANCE = (HTTPServer*)instance;
	while(INSTANCE->_isRunning) {
		event_base_dispatch(INSTANCE->_base);
	}
	LOG(INFO) << "HTTP Server stopped" << std::endl;
}

void HTTPServer::determineAddress() {
	char hostname[1024];
	gethostname(hostname, 1024);
	_address = std::string(hostname);
}

}