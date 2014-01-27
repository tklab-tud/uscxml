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

#include "InterpreterServlet.h"
#include "uscxml/Interpreter.h"
#include <glog/logging.h>

namespace uscxml {

InterpreterHTTPServlet::InterpreterHTTPServlet(InterpreterImpl* interpreter) {
	_interpreter = interpreter;

	std::stringstream path;
	path << _interpreter->getName();
	int i = 2;
	while(!HTTPServer::registerServlet(path.str(), this)) {
		path.clear();
		path.str();
		path << _interpreter->getName() << i++;
	}
	_path = path.str();
}

boost::shared_ptr<IOProcessorImpl> InterpreterHTTPServlet::create(InterpreterImpl* interpreter) {
	// we instantiate directly in Interpreter
	boost::shared_ptr<IOProcessorImpl> io = boost::shared_ptr<InterpreterHTTPServlet>(new InterpreterHTTPServlet(interpreter));
	return io;
}

bool InterpreterHTTPServlet::httpRecvRequest(const HTTPServer::Request& req) {
	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);

	//  evhttp_request_own(req.curlReq);

	_requests[toStr((uintptr_t)req.evhttpReq)] = req;

	Event event = req;

	event.name = "http." + event.data.compound["type"].atom;
	event.origin = toStr((uintptr_t)req.evhttpReq);

	if (event.data.compound["content"]) {
		if (event.data.compound["content"].compound.size() > 0) {
			std::map<std::string, Data>::iterator compoundIter = event.data.compound["content"].compound.begin();
			while(compoundIter != event.data.compound["content"].compound.end()) {
//				std::cout << compoundIter->second.atom << std::endl;
				Data json = Data::fromJSON(compoundIter->second.atom);
				if (json) {
//					std::cout << Data::toJSON(json) << std::endl;
					compoundIter->second = json;
				}
				compoundIter++;
			}
		}
	}

	_interpreter->receive(event);
	return true;
}

Data InterpreterHTTPServlet::getDataModelVariables() {
	Data data;
	if(_url.length() > 0)
		data.compound["location"] = Data(_url, Data::VERBATIM);
	return data;
}

void InterpreterHTTPServlet::send(const SendRequest& req) {
	LOG(ERROR) << "send not supported by http iorprocessor, use the fetch element";
}



InterpreterWebSocketServlet::InterpreterWebSocketServlet(InterpreterImpl* interpreter) {
	_interpreter = interpreter;

	std::stringstream path;
	path << _interpreter->getName();
	int i = 2;
	while(!HTTPServer::registerServlet(path.str(), this)) {
		path.clear();
		path.str();
		path << _interpreter->getName() << i++;
	}
	_path = path.str();
}

boost::shared_ptr<IOProcessorImpl> InterpreterWebSocketServlet::create(InterpreterImpl* interpreter) {
	// we instantiate directly in Interpreter
	boost::shared_ptr<IOProcessorImpl> io = boost::shared_ptr<InterpreterWebSocketServlet>(new InterpreterWebSocketServlet(interpreter));
	return io;
}

bool InterpreterWebSocketServlet::wsRecvRequest(struct evws_connection *conn, const HTTPServer::WSFrame& frame) {
	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);

	//  evhttp_request_own(req.curlReq);

	_requests[toStr((uintptr_t)conn)] = conn;

	Event event = frame;

	event.name = "ws." + event.data.compound["type"].atom;
	event.origin = toStr((uintptr_t)conn);

	if (event.data.compound["type"].atom.compare("text") == 0 && event.data.compound["content"]) {
		if (event.data.compound["content"].compound.size() > 0) {
			std::map<std::string, Data>::iterator compoundIter = event.data.compound["content"].compound.begin();
			while(compoundIter != event.data.compound["content"].compound.end()) {
				Data json = Data::fromJSON(compoundIter->second.atom);
				if (json) {
					compoundIter->second = json;
				}
				compoundIter++;
			}
		}
	}

	_interpreter->receive(event);
	return true;
}

Data InterpreterWebSocketServlet::getDataModelVariables() {
	Data data;
	if(_url.length() > 0)
		data.compound["location"] = Data(_url, Data::VERBATIM);
	return data;
}

void InterpreterWebSocketServlet::send(const SendRequest& req) {

	if (!req.data) {
		LOG(WARNING) << "No content given to send on websocket!";
		return;
	}

	if (_requests.find(req.target) != _requests.end()) {
		// send data to the given connection
		if (false) {
		} else if (req.data.binary) {
			HTTPServer::wsSend(_requests[req.target],
												 EVWS_BINARY_FRAME,
												 req.data.binary->data,
												 req.data.binary->size);
		} else if (req.data.node) {
			std::stringstream ssXML;
			ssXML << req.data.node;
			std::string data = ssXML.str();
			HTTPServer::wsSend(_requests[req.target],
												 EVWS_TEXT_FRAME,
												 data.c_str(),
												 data.length());
		} else if (req.data) {
			std::string data = Data::toJSON(req.data);
			HTTPServer::wsSend(_requests[req.target],
												 EVWS_TEXT_FRAME,
												 data.c_str(),
												 data.length());
		} else {
			LOG(WARNING) << "Not sure what to make off content given to send on websocket!";
		}
	} else if(req.target.size() && req.target.compare(0, 1, "/") == 0) {
		// broadcast to the given path
		if (false) {
		} else if (req.data.binary) {
			HTTPServer::wsBroadcast(req.target.c_str(),
															EVWS_BINARY_FRAME,
															req.data.binary->data,
															req.data.binary->size);
		} else if (req.data.node) {
			std::stringstream ssXML;
			ssXML << req.data.node;
			std::string data = ssXML.str();
			HTTPServer::wsBroadcast(req.target.c_str(),
															EVWS_TEXT_FRAME,
															data.c_str(),
															data.length());
		} else if (req.data) {
			std::string data = Data::toJSON(req.data);
			HTTPServer::wsBroadcast(req.target.c_str(),
															EVWS_TEXT_FRAME,
															data.c_str(),
															data.length());
		} else {
			LOG(WARNING) << "Not sure what to make off content given to broadcast on websocket!";
		}
	} else {
		LOG(WARNING) << "Invalid target for websocket";
	}
}

}