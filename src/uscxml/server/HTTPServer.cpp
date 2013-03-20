#include "uscxml/config.h"

#ifdef _WIN32
#include <winsock2.h>
#include <windows.h>
#endif

#include "uscxml/server/HTTPServer.h"
#include "uscxml/Message.h"
#include "uscxml/Factory.h"
#include <iostream>
#include <event2/dns.h>
#include <event2/event.h>
#include <event2/buffer.h>
#include <event2/http.h>
#include <event2/keyvalq_struct.h>
#include <event2/http_struct.h>
#include <event2/thread.h>

#include <string>
#include <iostream>

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

	evhttp_set_allowed_methods(_http,
	                           EVHTTP_REQ_GET |
	                           EVHTTP_REQ_POST |
	                           EVHTTP_REQ_HEAD |
	                           EVHTTP_REQ_PUT |
	                           EVHTTP_REQ_DELETE |
	                           EVHTTP_REQ_OPTIONS |
	                           EVHTTP_REQ_TRACE |
	                           EVHTTP_REQ_CONNECT |
	                           EVHTTP_REQ_PATCH); // allow all methods

	_handle = NULL;
	while((_handle = evhttp_bind_socket_with_handle(_http, INADDR_ANY, _port)) == NULL) {
		_port++;
	}
	determineAddress();

//	evhttp_set_timeout(_http, 5);

	// generic callback
	evhttp_set_gencb(_http, HTTPServer::httpRecvReqCallback, NULL);
}

HTTPServer::~HTTPServer() {
}

HTTPServer* HTTPServer::_instance = NULL;
tthread::recursive_mutex HTTPServer::_instanceMutex;
std::map<std::string, std::string> HTTPServer::mimeTypes;

HTTPServer* HTTPServer::getInstance(int port) {
//	tthread::lock_guard<tthread::recursive_mutex> lock(_instanceMutex);
	if (_instance == NULL) {

		// this is but a tiny list, supply a content-type <header> yourself
		mimeTypes["txt"] = "text/plain";
		mimeTypes["c"] = "text/plain";
		mimeTypes["h"] = "text/plain";
		mimeTypes["html"] = "text/html";
		mimeTypes["htm"] = "text/htm";
		mimeTypes["css"] = "text/css";
		mimeTypes["bmp"] = "image/bmp";
		mimeTypes["gif"] = "image/gif";
		mimeTypes["jpg"] = "image/jpeg";
		mimeTypes["jpeg"] = "image/jpeg";
		mimeTypes["mpg"] = "video/mpeg";
		mimeTypes["mov"] = "video/quicktime";
		mimeTypes["png"] = "image/png";
		mimeTypes["pdf"] = "application/pdf";
		mimeTypes["ps"] = "application/postscript";
		mimeTypes["tif"] = "image/tiff";
		mimeTypes["tiff"] = "image/tiff";

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

std::string HTTPServer::mimeTypeForExtension(const std::string& ext) {
	if (mimeTypes.find(ext) != mimeTypes.end())
		return mimeTypes[ext];
	return "";
}

void HTTPServer::httpRecvReqCallback(struct evhttp_request *req, void *callbackData) {
//  std::cout << (uintptr_t)req << ": Replying" << std::endl;
//  evhttp_send_error(req, 404, NULL);
//  return;

	evhttp_request_own(req);
	Request request;
	request.curlReq = req;

	switch (evhttp_request_get_command(req)) {
	case EVHTTP_REQ_GET:
		request.data.compound["type"] = Data("get", Data::VERBATIM);
		break;
	case EVHTTP_REQ_POST:
		request.data.compound["type"] = Data("post", Data::VERBATIM);
		break;
	case EVHTTP_REQ_HEAD:
		request.data.compound["type"] = Data("head", Data::VERBATIM);
		break;
	case EVHTTP_REQ_PUT:
		request.data.compound["type"] = Data("put", Data::VERBATIM);
		break;
	case EVHTTP_REQ_DELETE:
		request.data.compound["type"] = Data("delete", Data::VERBATIM);
		break;
	case EVHTTP_REQ_OPTIONS:
		request.data.compound["type"] = Data("options", Data::VERBATIM);
		break;
	case EVHTTP_REQ_TRACE:
		request.data.compound["type"] = Data("trace", Data::VERBATIM);
		break;
	case EVHTTP_REQ_CONNECT:
		request.data.compound["type"] = Data("connect", Data::VERBATIM);
		break;
	case EVHTTP_REQ_PATCH:
		request.data.compound["type"] = Data("patch", Data::VERBATIM);
		break;
	default:
		request.data.compound["type"] = Data("unknown", Data::VERBATIM);
		break;
	}

	struct evkeyvalq *headers;
	struct evkeyval *header;
	struct evbuffer *buf;

	// insert headers to event data
	headers = evhttp_request_get_input_headers(req);
	for (header = headers->tqh_first; header; header = header->next.tqe_next) {
		request.data.compound["header"].compound[header->key] = Data(header->value, Data::VERBATIM);
	}

	request.data.compound["remoteHost"] = Data(req->remote_host, Data::VERBATIM);
	request.data.compound["remotePort"] = Data(toStr(req->remote_port), Data::VERBATIM);
	request.data.compound["httpMajor"] = Data(toStr((unsigned short)req->major), Data::VERBATIM);
	request.data.compound["httpMinor"] = Data(toStr((unsigned short)req->minor), Data::VERBATIM);
	request.data.compound["uri"] = Data(HTTPServer::getBaseURL() + req->uri, Data::VERBATIM);
	request.data.compound["path"] = Data(evhttp_uri_get_path(evhttp_request_get_evhttp_uri(req)), Data::VERBATIM);

	// This was used for debugging
//	if (boost::ends_with(request.data.compound["path"].atom, ".png")) {
//		evhttp_send_error(req, 404, NULL);
//		return;
//	}

	// seperate path into components
	std::stringstream ss(request.data.compound["path"].atom);
	std::string item;
	while(std::getline(ss, item, '/')) {
		if (item.length() == 0)
			continue;
		request.data.compound["pathComponent"].array.push_back(Data(item, Data::VERBATIM));
	}

	// parse query string
	struct evkeyvalq params;
	struct evkeyval *param;
	const char* query = evhttp_uri_get_query(evhttp_request_get_evhttp_uri(req));

	evhttp_parse_query_str(query, &params);
	for (param = params.tqh_first; param; param = param->next.tqe_next) {
		request.data.compound["query"].compound[param->key] = Data(param->value, Data::VERBATIM);
	}
	evhttp_clear_headers(&params);

	// get content
	buf = evhttp_request_get_input_buffer(req);
	if (evbuffer_get_length(buf))
		request.data.compound["content"] = Data("", Data::VERBATIM);
	while (evbuffer_get_length(buf)) {
		int n;
		char cbuf[1024];
		n = evbuffer_remove(buf, cbuf, sizeof(buf)-1);
		if (n > 0) {
			request.data.compound["content"].atom.append(cbuf, n);
		}
	}

	// decode content
	if (request.data.compound.find("content") != request.data.compound.end() &&
	        request.data.compound["header"].compound.find("Content-Type") != request.data.compound["header"].compound.end()) {
		std::string contentType = request.data.compound["header"].compound["Content-Type"].atom;
		if (false) {
		} else if (boost::iequals(contentType, "application/x-www-form-urlencoded")) {
			request.data.compound["content"].atom = evhttp_decode_uri(request.data.compound["content"].atom.c_str());
		} else if (boost::iequals(contentType, "application/json")) {
			request.data.compound["content"] = Data::fromJSON(request.data.compound["content"].atom);
		}
	}
	
	if (callbackData == NULL) {
		HTTPServer::getInstance()->processByMatchingServlet(request);
	} else {
		((HTTPServlet*)callbackData)->httpRecvRequest(request);
	}
}

void HTTPServer::processByMatchingServlet(const Request& request) {
	servlet_iter_t servletIter = _servlets.begin();

	std::string actualPath = request.data.compound.at("path").atom;
	HTTPServlet* bestMatch = NULL;
	std::string bestPath;

	while(servletIter != _servlets.end()) {
		// is the servlet path a prefix of the actual path?
		std::string servletPath = "/" + servletIter->first;
		if (boost::iequals(actualPath.substr(0, servletPath.length()), servletPath) && // actual path is a prefix
				boost::iequals(actualPath.substr(servletPath.length(), 1), "/")) {         // and next character is a '/'
			if (bestPath.length() < servletPath.length()) {
				// this servlet is a better match
				bestPath = servletPath;
				bestMatch = servletIter->second;
			}
		}
		servletIter++;
	}

	if (bestMatch != NULL) {
		bestMatch->httpRecvRequest(request);
	} else {
		LOG(INFO) << "Got an HTTP request at " << actualPath << " but no servlet is registered there or at a prefix";
		evhttp_send_error(request.curlReq, 404, NULL);
	}
}

void HTTPServer::reply(const Reply& reply) {
	// we need to reply from the thread calling event_base_dispatch, just add to ist base queue!
	Reply* replyCB = new Reply(reply);
	HTTPServer* INSTANCE = getInstance();
	event_base_once(INSTANCE->_base, -1, EV_TIMEOUT, HTTPServer::replyCallback, replyCB, NULL);
}

void HTTPServer::replyCallback(evutil_socket_t fd, short what, void *arg) {

	Reply* reply = (Reply*)arg;

	if (reply->content.size() > 0 && reply->headers.find("Content-Type") == reply->headers.end()) {
		LOG(INFO) << "Sending content without Content-Type header";
	}

	std::map<std::string, std::string>::const_iterator headerIter = reply->headers.begin();
	while(headerIter != reply->headers.end()) {
		evhttp_add_header(evhttp_request_get_output_headers(reply->curlReq), headerIter->first.c_str(), headerIter->second.c_str());
		headerIter++;
	}

	if (reply->status >= 400) {
		evhttp_send_error(reply->curlReq, reply->status, NULL);
		return;
	}

	struct evbuffer *evb = NULL;

	if (!boost::iequals(reply->type, "HEAD") && reply->content.size() > 0) {
		evb = evbuffer_new();
		evbuffer_add(evb, reply->content.data(), reply->content.size());
	}

	evhttp_send_reply(reply->curlReq, reply->status, NULL, evb);

	if (evb != NULL)
		evbuffer_free(evb);
//  evhttp_request_free(reply->curlReq);
	delete(reply);
}

bool HTTPServer::registerServlet(const std::string& path, HTTPServlet* servlet) {
	HTTPServer* INSTANCE = getInstance();
	tthread::lock_guard<tthread::recursive_mutex> lock(INSTANCE->_mutex);

	// remove trailing and leading slash
	std::string actualPath = path;
	if (boost::ends_with(actualPath, "/"))
		actualPath = actualPath.substr(0, actualPath.size() - 1);
	if (boost::starts_with(actualPath, "/"))
		actualPath = actualPath.substr(1);
	std::string suffixedPath = actualPath;
	
	// if this servlet allows to adapt the path, do so
	int i = 2;
	while(INSTANCE->_servlets.find(suffixedPath) != INSTANCE->_servlets.end()) {
		if (!servlet->canAdaptPath())
			return false;
		std::stringstream ss;
		ss << actualPath << i++;
		suffixedPath = ss.str();
	}

	std::stringstream servletURL;
	servletURL << "http://" << INSTANCE->_address << ":" << INSTANCE->_port << "/" << suffixedPath;
	servlet->setURL(servletURL.str());

	INSTANCE->_servlets[suffixedPath] = servlet;

	LOG(INFO) << "HTTP Servlet listening at: " << servletURL.str() << std::endl;

	// register callback
	evhttp_set_cb(INSTANCE->_http, ("/" + suffixedPath).c_str(), HTTPServer::httpRecvReqCallback, servlet);

	return true;
}

std::string HTTPServer::getBaseURL() {
	HTTPServer* INSTANCE = getInstance();
	std::stringstream servletURL;
	servletURL << "http://" << INSTANCE->_address << ":" << INSTANCE->_port;
	return servletURL.str();
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