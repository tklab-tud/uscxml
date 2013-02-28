#include "HTTPServletInvoker.h"
#include <glog/logging.h>

#include "uscxml/config.h"

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool connect(pluma::Host& host) {
	host.add( new HTTPServletInvokerProvider() );
	return true;
}
#endif

HTTPServletInvoker::HTTPServletInvoker() {
	_isInterpreterGlobal = false;
}

HTTPServletInvoker::HTTPServletInvoker(Interpreter* interpreter) {
	_isInterpreterGlobal = true;
	_interpreter = interpreter;
	std::stringstream path;
	path << _interpreter->getName();
	int i = 2;
	while(!HTTPServer::registerServlet(path.str(), this)) {
		path.clear();
		path.str();
		path << _interpreter->getName() << toStr(i++);
	}
}

HTTPServletInvoker::~HTTPServletInvoker() {
	HTTPServer::unregisterServlet(this);

};

boost::shared_ptr<IOProcessorImpl> HTTPServletInvoker::create(Interpreter* interpreter) {
	boost::shared_ptr<HTTPServletInvoker> invoker = boost::shared_ptr<HTTPServletInvoker>(new HTTPServletInvoker());
	invoker->_interpreter = interpreter;
	return invoker;
}

Data HTTPServletInvoker::getDataModelVariables() {
	Data data;
	assert(_url.length() > 0);
	data.compound["location"] = Data(_url, Data::VERBATIM);
	return data;
}

void HTTPServletInvoker::send(const SendRequest& req) {
	assert(!_isInterpreterGlobal);

	if (req.name.find("reply.", 0, req.name.length())) {
		// this is a reply
		const std::string requestId = req.name.substr(6);
		if (_requests.find(requestId) == _requests.end()) {
			LOG(ERROR) << "Replying to non existing request " << requestId;
			return;
		}

		HTTPServer::Request httpRequest = _requests[requestId];
		HTTPServer::Reply httpReply(httpRequest);
		httpReply.content = req.content;

		std::map<std::string, std::string>::const_iterator nameListIter = req.namelist.begin();
		while(nameListIter != req.namelist.end()) {
			httpReply.headers[nameListIter->first] = nameListIter->second;
			nameListIter++;
		}

		std::multimap<std::string, std::string>::const_iterator paramIter = req.params.begin();
		while(paramIter != req.params.end()) {
			httpReply.headers[paramIter->first] = paramIter->second;
			paramIter++;
		}

		HTTPServer::reply(httpReply);
		return;
	}
}

void HTTPServletInvoker::cancel(const std::string sendId) {
	assert(!_isInterpreterGlobal);
}

void HTTPServletInvoker::invoke(const InvokeRequest& req) {
	assert(!_isInterpreterGlobal);

	_invokeId = req.invokeid;
	if (req.params.find("path") == req.params.end()) {
		LOG(ERROR) << "Path parameter required with httpserver";
	}
	_path = (*req.params.find("path")).second;

	if (req.params.find("callback") != req.params.end()) {
		_callback = (*req.params.find("callback")).second;
	} else {
		_callback = _path;
		std::replace(_callback.begin(), _callback.end(), '/', '.');
	}

	if (!HTTPServer::registerServlet(_path, this)) {
		LOG(ERROR) << "Cannot register http servlet at " << _path << ": " << " already taken";
	}
}

/**
 * Receive a request and deliver it to the interpreter
 */
void HTTPServletInvoker::httpRecvRequest(const HTTPServer::Request& req) {
	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);

//  evhttp_request_own(req.curlReq);

	_requests[toStr((uintptr_t)req.curlReq)] = req;

	Event event = req;

	if (_isInterpreterGlobal) {
		event.name = "http." + event.data.compound["type"].atom;
		event.origin = toStr((uintptr_t)req.curlReq);
	} else {
		event.name = _callback;
		event.data.compound["reqId"] = Data(toStr((uintptr_t)req.curlReq), Data::VERBATIM);
	}

	returnEvent(event);

}

std::string HTTPServletInvoker::getPath() {
	return _path;
}

}