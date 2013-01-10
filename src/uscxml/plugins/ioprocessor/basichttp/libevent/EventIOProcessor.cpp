#ifdef _WIN32
#include <winsock2.h>
#include <windows.h>
#endif

#include "uscxml/plugins/ioprocessor/basichttp/libevent/EventIOProcessor.h"
#include "uscxml/Message.h"
#include <iostream>
#include <event2/dns.h>
#include <event2/buffer.h>
#include <event2/keyvalq_struct.h>

#include <string.h>

#include <io/uri.hpp>
#include <glog/logging.h>

#ifndef _WIN32
#include <netdb.h>
#include <arpa/inet.h>
#endif

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool connect(pluma::Host& host) {
	host.add( new EventIOProcessorProvider() );
	return true;
}
#endif

// see http://www.w3.org/TR/scxml/#BasicHTTPEventProcessor

EventIOProcessor::EventIOProcessor() {
}

EventIOProcessor::~EventIOProcessor() {
	_asyncQueue.stop();
	evdns_base_free(_dns, 1);
	EventIOServer* httpServer = EventIOServer::getInstance();
	httpServer->unregisterProcessor(this);
}

IOProcessor* EventIOProcessor::create(Interpreter* interpreter) {
	EventIOProcessor* io = new EventIOProcessor();
	io->_interpreter = interpreter;

	io->_dns = evdns_base_new(io->_asyncQueue._eventLoop, 1);
	assert(io->_dns);
	assert(evdns_base_count_nameservers(io->_dns) > 0);

	// register at http server
	EventIOServer* httpServer = EventIOServer::getInstance();
	httpServer->registerProcessor(io);

	io->start();
	return io;
}

void EventIOProcessor::start() {
	_asyncQueue.start();
}

Data EventIOProcessor::getDataModelVariables() {
	Data data;
	assert(_url.length() > 0);
	data.compound["location"] = Data(_url, Data::VERBATIM);
	return data;
}


void EventIOProcessor::send(SendRequest& req) {
	// I cant figure out how to copy the reference into the struct :(
	_sendData[req.sendid].req = req;
	_sendData[req.sendid].ioProcessor = this;

	int err = 0;
	char uriBuf[1024];

	struct evhttp_uri* targetURI = evhttp_uri_parse(_sendData[req.sendid].req.target.c_str());
	if (evhttp_uri_get_port(targetURI) < 0)
		evhttp_uri_set_port(targetURI, 80);
	const char* hostName = evhttp_uri_get_host(targetURI);

	// use synchronous dns resolving for multicast dns
	if(hostName && strlen(hostName) >= strlen(".local")) {
		if(strcmp(hostName + strlen(hostName) - strlen(".local"), ".local") == 0) {
			evhttp_uri_set_host(targetURI, EventIOServer::syncResolve(hostName).c_str());
		}
	}
	evhttp_uri_join(targetURI, uriBuf, 1024);

	LOG(INFO) << "URI for send request: " << uriBuf << std::endl;

	int port = evhttp_uri_get_port(targetURI);
	if (port <= 0)
		port = 80;

	std::stringstream ssEndPoint;
	ssEndPoint << evhttp_uri_get_host(targetURI) << ":" << port;
	std::string endPoint = ssEndPoint.str();

	std::stringstream ssLocalURI;
	ssLocalURI << evhttp_uri_get_path(targetURI) << evhttp_uri_get_fragment(targetURI);
	std::string localURI = ssLocalURI.str();

	if (_httpConnections.find(endPoint) == _httpConnections.end())
		_httpConnections[endPoint] = evhttp_connection_base_new(_asyncQueue._eventLoop, _dns, evhttp_uri_get_host(targetURI), evhttp_uri_get_port(targetURI));

	struct evhttp_connection* httpConn = _httpConnections[endPoint];
	struct evhttp_request* httpReq = evhttp_request_new(EventIOProcessor::httpSendReqDone, this);

	// event name
	if (req.name.size() > 0) {
		evhttp_add_header(evhttp_request_get_output_headers(httpReq), "_scxmleventname", evhttp_encode_uri(req.name.c_str()));
	}

	// event namelist
	if (req.namelist.size() > 0) {
		std::map<std::string, std::string>::iterator namelistIter = req.namelist.begin();
		while (namelistIter != req.namelist.end()) {
			evhttp_add_header(evhttp_request_get_output_headers(httpReq),
			                  namelistIter->first.c_str(),
			                  evhttp_encode_uri(namelistIter->second.c_str()));
			namelistIter++;
		}
	}

	// event params
	if (req.params.size() > 0) {
		std::multimap<std::string, std::string>::iterator paramIter = req.params.begin();
		while (paramIter != req.params.end()) {
//      LOG(INFO) << paramIter->first << " = " << paramIter->second << std::endl;
			evhttp_add_header(evhttp_request_get_output_headers(httpReq),
			                  paramIter->first.c_str(),
			                  evhttp_encode_uri(paramIter->second.c_str()));
			paramIter++;
		}
	}

	// content
	if (req.content.size() > 0)
		evbuffer_add(evhttp_request_get_output_buffer(httpReq), req.content.c_str(), req.content.size());

#if 0
	evhttp_add_header(evhttp_request_get_output_headers(httpReq), "_scxmleventstruct", evhttp_encode_uri(req.toXMLString().c_str()));
#endif
	// required as per http 1.1 RFC2616 section 14.23
	evhttp_add_header(evhttp_request_get_output_headers(httpReq), "Host", evhttp_uri_get_host(targetURI));

	_httpRequests[req.sendid] = httpReq;
	err = evhttp_make_request(httpConn,
	                          httpReq,
	                          EVHTTP_REQ_POST, localURI.c_str());
	if (err) {
		LOG(ERROR) << "Could not make http request to " << req.target;
	}
}

void EventIOProcessor::httpRecvReq(struct evhttp_request *req, void *arg) {

	const char *cmdtype;
	struct evkeyvalq *headers;
	struct evkeyval *header;
	struct evbuffer *buf;

	switch (evhttp_request_get_command(req)) {
	case EVHTTP_REQ_GET:
		cmdtype = "GET";
		break;
	case EVHTTP_REQ_POST:
		cmdtype = "POST";
		break;
	case EVHTTP_REQ_HEAD:
		cmdtype = "HEAD";
		break;
	case EVHTTP_REQ_PUT:
		cmdtype = "PUT";
		break;
	case EVHTTP_REQ_DELETE:
		cmdtype = "DELETE";
		break;
	case EVHTTP_REQ_OPTIONS:
		cmdtype = "OPTIONS";
		break;
	case EVHTTP_REQ_TRACE:
		cmdtype = "TRACE";
		break;
	case EVHTTP_REQ_CONNECT:
		cmdtype = "CONNECT";
		break;
	case EVHTTP_REQ_PATCH:
		cmdtype = "PATCH";
		break;
	default:
		cmdtype = "unknown";
		break;
	}

	Event reqEvent;
	reqEvent.type = Event::EXTERNAL;
	bool scxmlStructFound = false;

	// map headers to event structure
	headers = evhttp_request_get_input_headers(req);
	for (header = headers->tqh_first; header;
	        header = header->next.tqe_next) {
//    std::cout << "Header: " << header->key << std::endl;
//    std::cout << "Value: " << evhttp_decode_uri(header->value) << std::endl;
		if (boost::iequals("_scxmleventstruct", header->key)) {
			reqEvent = Event::fromXML(evhttp_decode_uri(header->value));
			scxmlStructFound = true;
			break;
		} else if (boost::iequals("_scxmleventname", header->key)) {
			reqEvent.name = evhttp_decode_uri(header->value);
		} else {
			reqEvent.compound[header->key] = Data(evhttp_decode_uri(header->value), Data::VERBATIM);
		}
	}

	if (reqEvent.name.length() == 0)
		reqEvent.name = cmdtype;

	if (!scxmlStructFound) {
		// get content into event
		std::string content;
		buf = evhttp_request_get_input_buffer(req);
		while (evbuffer_get_length(buf)) {
			int n;
			char cbuf[128];
			n = evbuffer_remove(buf, cbuf, sizeof(buf)-1);
			if (n > 0) {
				content.append(cbuf, n);
			}
		}
		reqEvent.compound["content"] = Data(content, Data::VERBATIM);
	}

	EventIOProcessor* INSTANCE = (EventIOProcessor*)arg;
	INSTANCE->_interpreter->receive(reqEvent);

	evhttp_send_reply(req, 200, "OK", NULL);
}

void EventIOProcessor::httpSendReqDone(struct evhttp_request *req, void *cb_arg) {
	if (req) {
		LOG(INFO) << "got return code " << evhttp_request_get_response_code(req) << std::endl;
	}
}

EventIOServer::EventIOServer(unsigned short port) {
	_port = port;
	_base = event_base_new();
	_http = evhttp_new(_base);
	_handle = NULL;
	while((_handle = evhttp_bind_socket_with_handle(_http, INADDR_ANY, _port)) == NULL) {
		_port++;
	}
	determineAddress();
}

EventIOServer::~EventIOServer() {
}

EventIOServer* EventIOServer::_instance = NULL;
tthread::recursive_mutex EventIOServer::_instanceMutex;

EventIOServer* EventIOServer::getInstance() {
	tthread::lock_guard<tthread::recursive_mutex> lock(_instanceMutex);
	if (_instance == NULL) {
		_instance = new EventIOServer(8080);
		_instance->start();
	}
	return _instance;
}

void EventIOServer::registerProcessor(EventIOProcessor* processor) {
	EventIOServer* INSTANCE = getInstance();
	tthread::lock_guard<tthread::recursive_mutex> lock(INSTANCE->_mutex);

	/**
	 * Determine path for interpreter.
	 *
	 * If the interpreter has a name and it is not yet taken, choose it as the path
	 * for requests. If the interpreters name path is already taken, append digits
	 * until we have an available path.
	 *
	 * If the interpreter does not specify a name, take its sessionid.
	 */

	std::string path = processor->_interpreter->getName();
	if (path.size() == 0) {
		path = processor->_interpreter->getSessionId();
	}
	assert(path.size() > 0);

	std::stringstream actualPath(path);
	int i = 1;
	while(INSTANCE->_processors.find(actualPath.str()) != INSTANCE->_processors.end()) {
		actualPath.str(std::string());
		actualPath.clear();
		actualPath << path << ++i;
	}

	std::stringstream processorURL;
	processorURL << "http://" << INSTANCE->_address << ":" << INSTANCE->_port << "/" << actualPath.str();

	INSTANCE->_processors[actualPath.str()] = processor;
	processor->setURL(processorURL.str());

	LOG(INFO) << "SCXML listening at: " << processorURL.str() << std::endl;

	evhttp_set_cb(INSTANCE->_http, ("/" + actualPath.str()).c_str(), EventIOProcessor::httpRecvReq, processor);
//  evhttp_set_cb(THIS->_http, "/", EventIOProcessor::httpRecvReq, processor);
//  evhttp_set_gencb(THIS->_http, EventIOProcessor::httpRecvReq, NULL);
}

void EventIOServer::unregisterProcessor(EventIOProcessor* processor) {
	EventIOServer* INSTANCE = getInstance();
	tthread::lock_guard<tthread::recursive_mutex> lock(INSTANCE->_mutex);
	evhttp_del_cb(INSTANCE->_http, processor->_url.c_str());
}

void EventIOServer::start() {
	_isRunning = true;
	_thread = new tthread::thread(EventIOServer::run, this);
}

void EventIOServer::run(void* instance) {
	EventIOServer* INSTANCE = (EventIOServer*)instance;
	while(INSTANCE->_isRunning) {
		event_base_dispatch(INSTANCE->_base);
	}
	LOG(INFO) << "HTTP Server stopped" << std::endl;
}

std::string EventIOServer::syncResolve(const std::string& hostname) {
	struct hostent *he;
	struct in_addr **addr_list;
	int i;

	if ( (he = gethostbyname( hostname.c_str() ) ) != NULL) {
		addr_list = (struct in_addr **) he->h_addr_list;
		for(i = 0; addr_list[i] != NULL; i++) {
			return std::string(inet_ntoa(*addr_list[i]));
		}
	}
	return "";
}

void EventIOServer::determineAddress() {

	char hostname[1024];
	gethostname(hostname, 1024);
	_address = std::string(hostname);

#if 0
	struct sockaddr_storage ss;
	evutil_socket_t fd;
	ev_socklen_t socklen = sizeof(ss);
	char addrbuf[128];

	void *inaddr;
	const char *addr;
	int got_port = -1;
	fd = evhttp_bound_socket_get_fd(_handle);
	memset(&ss, 0, sizeof(ss));
	if (getsockname(fd, (struct sockaddr *)&ss, &socklen)) {
		perror("getsockname() failed");
		return;
	}

	if (ss.ss_family == AF_INET) {
		got_port = ntohs(((struct sockaddr_in*)&ss)->sin_port);
		inaddr = &((struct sockaddr_in*)&ss)->sin_addr;
	} else if (ss.ss_family == AF_INET6) {
		got_port = ntohs(((struct sockaddr_in6*)&ss)->sin6_port);
		inaddr = &((struct sockaddr_in6*)&ss)->sin6_addr;
	} else {
		fprintf(stderr, "Weird address family %d\n",
		        ss.ss_family);
		return;
	}
	addr = evutil_inet_ntop(ss.ss_family, inaddr, addrbuf,
	                        sizeof(addrbuf));
	if (addr) {
		_address = std::string(addr);
	} else {
		fprintf(stderr, "evutil_inet_ntop failed\n");
		return;
	}
#endif
}

}