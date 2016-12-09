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
#include "uscxml/messages/Event.h"
#include "uscxml/util/DOM.h"

#include <iostream>
#include <event2/dns.h>
#include <event2/buffer.h>
#include <event2/keyvalq_struct.h>

#include <string.h>

#include "uscxml/interpreter/Logging.h"
#include <boost/algorithm/string.hpp>

#ifdef _WIN32
#define NOMINMAX
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
	HTTPServer::getInstance();
}

BasicHTTPIOProcessor::~BasicHTTPIOProcessor() {
	HTTPServer* httpServer = HTTPServer::getInstance();
	httpServer->unregisterServlet(this);
}


std::shared_ptr<IOProcessorImpl> BasicHTTPIOProcessor::create(InterpreterImpl* interpreter) {
	std::shared_ptr<BasicHTTPIOProcessor> io(new BasicHTTPIOProcessor());
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

	std::list<std::string> pathComps = url.pathComponents();
	std::list<std::string>::const_iterator pathCompIter = pathComps.begin();
	while(pathCompIter != pathComps.end()) {
		data.compound["pathComponents"].array.push_back(Data(*pathCompIter, Data::VERBATIM));
		pathCompIter++;
	}

	return data;
}

bool BasicHTTPIOProcessor::requestFromHTTP(const HTTPServer::Request& req) {
	Event event = req;
	event.eventType = Event::EXTERNAL;

//	std::cout << req.raw << std::endl;

	/**
	 * If a single instance of the parameter '_scxmleventname' is present, the
	 * SCXML Processor must use its value as the name of the SCXML event that it
	 * raises.
	 */

	{
		// if we sent ourself an event it will end up here
		// this will call the const subscript operator
		if (req.data.at("content").hasKey("_scxmleventname")) {
			event.name = req.data.at("content").at("_scxmleventname").atom;
		}
		if (req.data.at("content").hasKey("content")) {
			event.data.atom = req.data.at("content").at("content").atom;
		}
	}

	// if we used wget, it will end up here - unify?
	if (req.data.hasKey("content")) {
		const Data& data = req.data["content"];
		for(std::map<std::string, Data>::const_iterator compIter = data.compound.begin();
		        compIter!= data.compound.end(); compIter++) {
			if (compIter->first == "content") {
				event.data.atom = compIter->second.atom;
			} else {
				event.data[compIter->first] = compIter->second;
			}
		}
	}

	if (req.data.hasKey("header")) {
		const Data& data = req.data["header"];
		for(std::map<std::string, Data>::const_iterator compIter = data.compound.begin();
		        compIter!= data.compound.end(); compIter++) {
			if (compIter->first == "_scxmleventname") {
				event.name = compIter->second.atom;
			}
		}
	}

	// test 532
	if (event.name.length() == 0)
		event.name = "http." + req.data.compound.at("type").atom;

	eventToSCXML(event, USCXML_IOPROC_BASICHTTP_TYPE, _url);
	evhttp_send_reply(req.evhttpReq, 200, "OK", NULL);
	return true;
}

bool BasicHTTPIOProcessor::isValidTarget(const std::string& target) {
	try {
		URL url(target);
		if (url.scheme().compare("http") != 0)
			return false;

		return true;
	} catch (ErrorEvent e) {
	}
	return false;
}

void BasicHTTPIOProcessor::eventFromSCXML(const std::string& target, const Event& event) {

	// TODO: is this still needed with isValidTarget()?
	if (target.length() == 0) {
		_interpreter->enqueueInternal(Event("error.communication", Event::PLATFORM));
		return;
	}

	bool isLocal = target == _url;
	URL targetURL(target);
	std::stringstream kvps;
	std::string kvpSeperator;

	// event name
	if (event.name.size() > 0) {
		char* eventNameCStr = evhttp_encode_uri("_scxmleventname");
		char* eventValueCStr = evhttp_encode_uri(event.name.c_str());
		kvps << kvpSeperator << eventNameCStr << "=" << eventValueCStr;
		kvpSeperator = "&";
		targetURL.addOutHeader("_scxmleventname", eventValueCStr);
		free(eventNameCStr);
		free(eventValueCStr);
	}

	// event namelist
	if (event.namelist.size() > 0) {
		std::map<std::string, Data>::const_iterator namelistIter = event.namelist.begin();
		while (namelistIter != event.namelist.end()) {
			char* keyCStr = evhttp_encode_uri(namelistIter->first.c_str());
			// this is simplified - Data might be more elaborate than a simple string atom
			char* valueCStr = evhttp_encode_uri(namelistIter->second.atom.c_str());
			kvps << kvpSeperator << keyCStr << "=" << valueCStr;
			free(keyCStr);
			free(valueCStr);
			kvpSeperator = "&";
			targetURL.addOutHeader(namelistIter->first, namelistIter->second);
			namelistIter++;
		}
	}

	// event params
	if (event.params.size() > 0) {
		std::multimap<std::string, Data>::const_iterator paramIter = event.params.begin();
		while (paramIter != event.params.end()) {
			char* keyCStr = evhttp_encode_uri(paramIter->first.c_str());
			// this is simplified - Data might be more elaborate than a simple string atom
			char* valueCStr = evhttp_encode_uri(paramIter->second.atom.c_str());
			kvps << kvpSeperator << keyCStr << "=" << valueCStr;
			free(keyCStr);
			free(valueCStr);
			kvpSeperator = "&";
			targetURL.addOutHeader(paramIter->first, paramIter->second);
			paramIter++;
		}
	}

	// try hard to find actual content
	char* keyCStr = evhttp_encode_uri("content");
	if (!event.data.empty()) {
		char* valueCStr = NULL;
		if (event.data.atom.length() || event.data.array.size() || event.data.compound.size()) {
			valueCStr = evhttp_encode_uri(Data::toJSON(event.data).c_str());
		} else if(event.data.node) {
			std::stringstream xmlStream;
			xmlStream << event.data.node;
			valueCStr = evhttp_encode_uri(xmlStream.str().c_str());
		} else if(event.data.binary) {
			valueCStr = evhttp_encode_uri(event.data.binary.base64().c_str());
		}
		if (valueCStr != NULL) {
			kvps << kvpSeperator << keyCStr << "=" << valueCStr;
			free(valueCStr);
			kvpSeperator = "&";
		}
	}
	free(keyCStr);

	targetURL.setOutContent(kvps.str());
	targetURL.addOutHeader("Content-Type", "application/x-www-form-urlencoded");

	targetURL.setRequestType(URLRequestType::POST);
	targetURL.addMonitor(this);

	_sendRequests[event.sendid] = std::make_pair(targetURL, event);
	if (isLocal) {
		// test201 use a blocking request with local communication
		targetURL.download(true);
	} else {
		URLFetcher::fetchURL(targetURL);
	}
}

void BasicHTTPIOProcessor::downloadStarted(const URL& url) {}

void BasicHTTPIOProcessor::downloadCompleted(const URL& url) {
	std::map<std::string, std::pair<URL, Event> >::iterator reqIter = _sendRequests.begin();
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
				eventToSCXML(event, USCXML_IOPROC_BASICHTTP_TYPE, std::string(_url));
			}
			_sendRequests.erase(reqIter);
			return;
		}
		reqIter++;
	}
	assert(false);
}

void BasicHTTPIOProcessor::downloadFailed(const URL& url, int errorCode) {

	std::map<std::string, std::pair<URL, Event> >::iterator reqIter = _sendRequests.begin();
	while(reqIter != _sendRequests.end()) {
		if (reqIter->second.first == url) {
			Event failEvent;
			failEvent.name = "error.communication";
			eventToSCXML(failEvent, USCXML_IOPROC_BASICHTTP_TYPE, std::string(_url));

			_sendRequests.erase(reqIter);
			return;
		}
		reqIter++;
	}
	assert(false);

}


}
