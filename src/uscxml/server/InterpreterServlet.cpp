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

InterpreterServlet::InterpreterServlet(InterpreterImpl* interpreter) {
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

boost::shared_ptr<IOProcessorImpl> InterpreterServlet::create(InterpreterImpl* interpreter) {
	// we instantiate directly in Interpreter
	boost::shared_ptr<IOProcessorImpl> io = boost::shared_ptr<InterpreterServlet>(new InterpreterServlet(interpreter));
	return io;
}

bool InterpreterServlet::httpRecvRequest(const HTTPServer::Request& req) {
	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);

	//  evhttp_request_own(req.curlReq);

	_requests[toStr((uintptr_t)req.curlReq)] = req;

	Event event = req;

	event.name = "http." + event.data.compound["type"].atom;
	event.origin = toStr((uintptr_t)req.curlReq);

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

Data InterpreterServlet::getDataModelVariables() {
	Data data;
	assert(_url.length() > 0);
	data.compound["location"] = Data(_url, Data::VERBATIM);
	return data;
}

void InterpreterServlet::send(const SendRequest& req) {
	LOG(ERROR) << "send not supported by http iorprocessor, use the fetch element";
}

}