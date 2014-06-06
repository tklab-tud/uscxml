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

#include "uscxml/Common.h"

#include "uscxml/plugins/ioprocessor/basichttp/BasicHTTPIOProcessor.h"
#include "uscxml/Message.h"
#include "uscxml/DOMUtils.h"
#include <iostream>
#include <event2/dns.h>
#include <event2/buffer.h>
#include <event2/keyvalq_struct.h>

#include <string.h>

#include <io/uri.hpp>
#include <glog/logging.h>
#include <boost/algorithm/string.hpp>

#ifdef _WIN32
#include <winsock2.h>
#include <windows.h>
#endif

#ifndef _WIN32
#include <netdb.h>
#include <arpa/inet.h>
#endif

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

#ifndef ioprocessor_scxml_EXPORTS
#	ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool pluginConnect(pluma::Host& host) {
	host.add( new BasicHTTPIOProcessorProvider() );
	return true;
}
#	endif
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

	// we are not connected!
	if(_url.length() == 0)
		return data;

	data.compound["location"] = Data(_url, Data::VERBATIM);

	URL url(_url);
	data.compound["host"] = Data(url.host(), Data::VERBATIM);
	data.compound["port"] = Data(url.port(), Data::VERBATIM);
	data.compound["path"] = Data(url.path(), Data::VERBATIM);
	data.compound["scheme"] = Data(url.scheme(), Data::VERBATIM);

	std::vector<std::string> pathComps = url.pathComponents();
	std::vector<std::string>::const_iterator pathCompIter = pathComps.begin();
	while(pathCompIter != pathComps.end()) {
		data.compound["pathComponens"].array.push_back(Data(*pathCompIter, Data::VERBATIM));
		pathCompIter++;
	}

	return data;
}

bool BasicHTTPIOProcessor::httpRecvRequest(const HTTPServer::Request& req) {
	Event reqEvent = req;
	reqEvent.eventType = Event::EXTERNAL;

//	std::cout << req.raw << std::endl;

	/**
	 * If a single instance of the parameter '_scxmleventname' is present, the
	 * SCXML Processor must use its value as the name of the SCXML event that it
	 * raises.
	 */

	// this will call the const subscript operator
	if (req.data.at("content").hasKey("_scxmleventname")) {
		reqEvent.name = req.data.at("content").at("_scxmleventname").atom;
	}
	if (req.data.at("content").hasKey("content")) {
		reqEvent.content = req.data.at("content").at("content").atom;
	}

	// check whether we can parse it as XML
	if (reqEvent.content.length() > 0) {
		NameSpacingParser parser = NameSpacingParser::fromXML(reqEvent.content);
		if (!parser.errorsReported()) {
			reqEvent.dom = parser.getDocument();
		}
	}

	/// test532
	if (reqEvent.name.length() == 0)
		reqEvent.name = "http." + req.data.compound.at("type").atom;

	returnEvent(reqEvent);
	evhttp_send_reply(req.evhttpReq, 200, "OK", NULL);
	return true;
}

void BasicHTTPIOProcessor::send(const SendRequest& req) {

	if (req.target.length() == 0) {
		_interpreter->receiveInternal(Event("error.communication", Event::PLATFORM));
		return;
	}

	bool isLocal = false;
	std::string target;
	if (!boost::equals(req.target, _url)) {
		target = req.target;
	} else {
		isLocal = true;
		target = _url;
	}
	URL targetURL(target);
	std::stringstream kvps;
	std::string kvpSeperator;

	// event name
	if (req.name.size() > 0) {
		char* eventNameCStr = evhttp_encode_uri("_scxmleventname");
		char* eventValueCStr = evhttp_encode_uri(req.name.c_str());
		kvps << kvpSeperator << eventNameCStr << "=" << eventValueCStr;
		kvpSeperator = "&";
		free(eventNameCStr);
		free(eventValueCStr);
//		targetURL.addOutHeader("_scxmleventname", evhttp_encode_uri(req.name.c_str()));
	}

	// event namelist
	if (req.namelist.size() > 0) {
		std::map<std::string, Data>::const_iterator namelistIter = req.namelist.begin();
		while (namelistIter != req.namelist.end()) {
			char* keyCStr = evhttp_encode_uri(namelistIter->first.c_str());
			// this is simplified - Data might be more elaborate than a simple string atom
			char* valueCStr = evhttp_encode_uri(namelistIter->second.atom.c_str());
			kvps << kvpSeperator << keyCStr << "=" << valueCStr;
			free(keyCStr);
			free(valueCStr);
			kvpSeperator = "&";
//			targetURL.addOutHeader(namelistIter->first, namelistIter->second);
			namelistIter++;
		}
	}

	// event params
	if (req.params.size() > 0) {
		std::multimap<std::string, Data>::const_iterator paramIter = req.params.begin();
		while (paramIter != req.params.end()) {
			char* keyCStr = evhttp_encode_uri(paramIter->first.c_str());
			// this is simplified - Data might be more elaborate than a simple string atom
			char* valueCStr = evhttp_encode_uri(paramIter->second.atom.c_str());
			kvps << kvpSeperator << keyCStr << "=" << valueCStr;
			free(keyCStr);
			free(valueCStr);
			kvpSeperator = "&";
//			targetURL.addOutHeader(paramIter->first, paramIter->second);
			paramIter++;
		}
	}

	// try hard to find actual content
	char* keyCStr = evhttp_encode_uri("content");
	if (req.content.size() > 0) {
		char* valueCStr = evhttp_encode_uri(req.content.c_str());
		kvps << kvpSeperator << keyCStr << "=" << valueCStr;
		free(valueCStr);
		kvpSeperator = "&";
	} else if (req.dom) {
		std::stringstream xmlStream;
		xmlStream << req.dom;
		char* valueCStr = evhttp_encode_uri(xmlStream.str().c_str());
		kvps << kvpSeperator << keyCStr << "=" << valueCStr;
		free(valueCStr);
		kvpSeperator = "&";
	} else if (!req.data.empty()) {
		char* valueCStr = NULL;
		if (req.data.atom.length() || req.data.array.size() || req.data.compound.size()) {
			valueCStr = evhttp_encode_uri(Data::toJSON(req.data).c_str());
		} else if(req.data.node) {
			std::stringstream xmlStream;
			xmlStream << req.data.node;
			valueCStr = evhttp_encode_uri(xmlStream.str().c_str());
		} else if(req.data.binary) {
			valueCStr = evhttp_encode_uri(req.data.binary->base64().c_str());
		}
		if (valueCStr != NULL) {
			kvps << kvpSeperator << keyCStr << "=" << valueCStr;
			free(valueCStr);
			kvpSeperator = "&";
		}
	}
	free(keyCStr);

	targetURL.setOutContent(kvps.str());

//	targetURL.addOutHeader("Content-Type", "application/x-www-form-urlencoded");

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
			// test513
			std::string statusCode = url.getStatusCode();
			if (statusCode.length() > 0) {
				std::string statusPrefix = statusCode.substr(0,1);
				std::string statusRest = statusCode.substr(1);
				Event event;
				event.data = url;
				event.name = "HTTP." + statusPrefix + "." + statusRest;
				returnEvent(event);
			}
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