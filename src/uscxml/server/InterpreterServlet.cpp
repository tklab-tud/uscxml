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

void InterpreterServlet::httpRecvRequest(const HTTPServer::Request& req) {
	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);

	//  evhttp_request_own(req.curlReq);

	_requests[toStr((uintptr_t)req.curlReq)] = req;

	Event event = req;

	event.name = "http." + event.data.compound["type"].atom;
	event.origin = toStr((uintptr_t)req.curlReq);
	event.initContent(event.data.compound["content"].atom);
	_interpreter->receive(event);
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