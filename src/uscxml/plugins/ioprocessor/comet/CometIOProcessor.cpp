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

#include <uscxml/Common.h>
#include "uscxml/plugins/ioprocessor/comet/CometIOProcessor.h"
#include "uscxml/Message.h"
#include <iostream>

#include <string.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool pluginConnect(pluma::Host& host) {
	host.add( new CometIOProcessorProvider() );
	return true;
}
#endif

CometIOProcessor::CometIOProcessor() {
}

CometIOProcessor::~CometIOProcessor() {
}

boost::shared_ptr<IOProcessorImpl> CometIOProcessor::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<CometIOProcessor> io = boost::shared_ptr<CometIOProcessor>(new CometIOProcessor());
	io->_interpreter = interpreter;

	// register at http server
	std::string path = interpreter->getName();
	int i = 2;
	while (!HTTPServer::registerServlet(path + "/comet", io.get())) {
		std::stringstream ss;
		ss << interpreter->getName() << i++;
		path = ss.str();
	}

	return io;
}

Data CometIOProcessor::getDataModelVariables() {
	Data data;
	return data;
}

void CometIOProcessor::send(const SendRequest& req) {
	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
	if (!_longPollingReq) {
		_outQueue.push_back(req);
		return;
	}
	reply(req, _longPollingReq);
}

void CometIOProcessor::reply(const SendRequest& req, const HTTPServer::Request& longPoll) {
	HTTPServer::Reply reply(longPoll);

	if (req.dom) {
		std::stringstream ss;
		ss << req.dom;
		reply.content = ss.str();
		reply.headers["Content-Type"] = "application/xml";
	} else if (req.data) {
		reply.content = Data::toJSON(req.data);
		reply.headers["Content-Type"] = "application/json";
	} else if (req.content.length() > 0) {
		reply.content = req.content;
		reply.headers["Content-Type"] = "text/plain";
	}

	if (req.params.find("Content-Type") != req.params.end())
		reply.headers["Content-Type"] = req.params.find("Content-Type")->first;

	HTTPServer::reply(reply);
}

bool CometIOProcessor::httpRecvRequest(const HTTPServer::Request& request) {
	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);

	if (_longPollingReq)
		// send 204 to last request and remember new one
		evhttp_send_error(_longPollingReq.evhttpReq, 204, NULL);
	_longPollingReq = request;
	if (!_outQueue.empty()) {
		send(_outQueue.front());
		_outQueue.pop_front();
	}
	return true;
}

}