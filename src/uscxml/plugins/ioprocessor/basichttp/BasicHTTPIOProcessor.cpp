#ifdef _WIN32
#include <winsock2.h>
#include <windows.h>
#endif

#include "uscxml/plugins/ioprocessor/basichttp/BasicHTTPIOProcessor.h"
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
	host.add( new BasicHTTPIOProcessorProvider() );
	return true;
}
#endif

// see http://www.w3.org/TR/scxml/#BasicHTTPEventProcessor

BasicHTTPIOProcessor::BasicHTTPIOProcessor() {
}

BasicHTTPIOProcessor::~BasicHTTPIOProcessor() {
	HTTPServer* httpServer = HTTPServer::getInstance();
	httpServer->unregisterServlet(this);
}


boost::shared_ptr<IOProcessorImpl> BasicHTTPIOProcessor::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<BasicHTTPIOProcessor> io = boost::shared_ptr<BasicHTTPIOProcessor>(new BasicHTTPIOProcessor());
	io->_interpreter = interpreter;

	// register at http server
	std::string path = interpreter->getName();
	int i = 2;
	while (!HTTPServer::registerServlet(path + "/basichttp", io.get())) {
		std::stringstream ss;
		ss << interpreter->getName() << i++;
		path = ss.str();
	}

	return io;
}

Data BasicHTTPIOProcessor::getDataModelVariables() {
	Data data;
	assert(_url.length() > 0);
	data.compound["location"] = Data(_url, Data::VERBATIM);
	return data;
}

void BasicHTTPIOProcessor::httpRecvRequest(const HTTPServer::Request& req) {
	Event reqEvent = req;
	reqEvent.type = Event::EXTERNAL;
	bool scxmlStructFound = false;

	if (reqEvent.data.compound["header"].compound.find("_scxmleventstruct") != reqEvent.data.compound["header"].compound.end()) {
		// TODO: this looses all other information
		reqEvent = Event::fromXML(evhttp_decode_uri(reqEvent.data.compound["header"].compound["_scxmleventstruct"].atom.c_str()));
		scxmlStructFound = true;
	}
	if (reqEvent.data.compound["header"].compound.find("_scxmleventname") != reqEvent.data.compound["header"].compound.end()) {
		reqEvent.name = evhttp_decode_uri(reqEvent.data.compound["header"].compound["_scxmleventname"].atom.c_str());
	}

	std::map<std::string, Data>::iterator headerIter = reqEvent.data.compound["header"].compound.begin();
	while(headerIter != reqEvent.data.compound["header"].compound.end()) {
		reqEvent.data.compound[headerIter->first] = Data(evhttp_decode_uri(headerIter->second.atom.c_str()), Data::VERBATIM);
		headerIter++;
	}

#if 0
	std::map<std::string, std::string>::const_iterator headerIter = req.headers.begin();
	while(headerIter != req.headers.end()) {
		if (boost::iequals("_scxmleventstruct", headerIter->first)) {
			reqEvent = Event::fromXML(evhttp_decode_uri(headerIter->second.c_str()));
			scxmlStructFound = true;
			break;
		} else if (boost::iequals("_scxmleventname", headerIter->first)) {
			reqEvent.name = evhttp_decode_uri(headerIter->second.c_str());
		} else {
			reqEvent.data.compound[headerIter->first] = Data(evhttp_decode_uri(headerIter->second.c_str()), Data::VERBATIM);
		}
		headerIter++;
	}
#endif

	if (reqEvent.name.length() == 0)
		reqEvent.name = req.type;

	if (!scxmlStructFound) {
		// get content into event
		reqEvent.data.compound["content"] = Data(req.content, Data::VERBATIM);
	}

	returnEvent(reqEvent);
	evhttp_send_reply(req.curlReq, 200, "OK", NULL);
}

void BasicHTTPIOProcessor::send(const SendRequest& req) {

	bool isLocal = false;
	std::string target;
	if (req.target.length() > 0) {
		target = req.target;
	} else {
		isLocal = true;
		target = _url;
	}
	URL targetURL(target);

	// event name
	if (req.name.size() > 0) {
		targetURL.addOutHeader("_scxmleventname", evhttp_encode_uri(req.name.c_str()));
	}

	// event namelist
	if (req.namelist.size() > 0) {
		std::map<std::string, std::string>::const_iterator namelistIter = req.namelist.begin();
		while (namelistIter != req.namelist.end()) {
			targetURL.addOutHeader(namelistIter->first, namelistIter->second);
			namelistIter++;
		}
	}

	// event params
	if (req.params.size() > 0) {
		std::multimap<std::string, std::string>::const_iterator paramIter = req.params.begin();
		while (paramIter != req.params.end()) {
			targetURL.addOutHeader(paramIter->first, paramIter->second);
			paramIter++;
		}
	}

	// content
	if (req.content.size() > 0)
		targetURL.setOutContent(req.content);

	targetURL.setRequestType("post");
	targetURL.addMonitor(this);

	_sendRequests[req.sendid] = std::make_pair(targetURL, req);
	if (isLocal) {
		// test201 use a blocking request with local communication
		targetURL.download(true);
	} else {
		URLFetcher::fetchURL(targetURL);
	}
}

void BasicHTTPIOProcessor::downloadStarted(const URL& url) {}

void BasicHTTPIOProcessor::downloadCompleted(const URL& url) {
	std::map<std::string, std::pair<URL, SendRequest> >::iterator reqIter = _sendRequests.begin();
	while(reqIter != _sendRequests.end()) {
		if (reqIter->second.first == url) {
			_sendRequests.erase(reqIter);
			return;
		}
		reqIter++;
	}
	assert(false);
}

void BasicHTTPIOProcessor::downloadFailed(const URL& url, int errorCode) {

	std::map<std::string, std::pair<URL, SendRequest> >::iterator reqIter = _sendRequests.begin();
	while(reqIter != _sendRequests.end()) {
		if (reqIter->second.first == url) {
			Event failEvent;
			failEvent.name = "error.communication";
			returnEvent(failEvent);

			_sendRequests.erase(reqIter);
			return;
		}
		reqIter++;
	}
	assert(false);

}


}