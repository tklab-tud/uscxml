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

#include <boost/algorithm/string.hpp>

#include <uscxml/config.h>
#include "XHTMLInvoker.h"
#include <glog/logging.h>
#include "uscxml/DOMUtils.h"
#include <uscxml/plugins/ioprocessor/comet/CometIOProcessor.h>
#include <DOM/io/Stream.hpp>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

#if __APPLE__
#	if TARGET_OS_IPHONE || TARGET_IPHONE_SIMULATOR
#	else
#	include <CoreFoundation/CFBundle.h>
#	include <ApplicationServices/ApplicationServices.h>
#	endif
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool pluginConnect(pluma::Host& host) {
	host.add( new XHTMLInvokerProvider() );
	return true;
}
#endif

XHTMLInvoker::XHTMLInvoker() {
}

XHTMLInvoker::~XHTMLInvoker() {
};

boost::shared_ptr<InvokerImpl> XHTMLInvoker::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<XHTMLInvoker> invoker = boost::shared_ptr<XHTMLInvoker>(new XHTMLInvoker());
	invoker->_interpreter = interpreter;
//	_ioProc = interpreter->getFactory()->createIOProcessor("comet", interpreter);
	return invoker;
}

bool XHTMLInvoker::httpRecvRequest(const HTTPServer::Request& req) {
	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);

	// these are the XHR requests
	if (iequals(req.data["header"]["X-Requested-With"].atom, "XMLHttpRequest")) {
		if (iequals(req.data["type"].atom, "get")) {
			// the long-polling GET
			if (_longPoll) {
				evhttp_send_error(_longPoll.evhttpReq, 204, NULL);
				_longPoll.evhttpReq = NULL;
			}
			_longPoll = req;
			if (!_outQueue.empty()) {
				send(_outQueue.front());
				_outQueue.pop_front();
			}
			return true;
		} else {
			// a POST request
			Event ev(req);
			if (ev.data["header"]["X-SCXML-Name"]) {
				ev.name = ev.data["header"]["X-SCXML-Name"].atom;
			} else {
				ev.name = req.data["type"].atom;
			}
			ev.origin = _invokeId;
			ev.initContent(req.data["content"].atom);
			ev.data.compound["Connection"] = req.data;
			// content is already on ev.raw
			ev.data.compound["Connection"].compound.erase("content");

			HTTPServer::Reply reply(req);
			HTTPServer::reply(reply);

			returnEvent(ev);
			return true;
		}
	}

	// initial request for a document
	if (!req.data["query"] && // no query parameters
	        iequals(req.data["type"].atom, "get") && // request type is GET
	        req.content.length() == 0) { // no content

		HTTPServer::Reply reply(req);

		std::string content;
		std::stringstream ss;
		if (_invokeReq.dom) {
//			ss << _invokeReq.getFirstDOMElement();
			ss << _invokeReq.dom;
			content = ss.str();
		} else if(_invokeReq.data) {
			ss << _invokeReq.data;
			content = ss.str();
		} else if (_invokeReq.content.length() > 0) {
			content = _invokeReq.content;
		} else {
			URL templateURL("templates/xhtml-invoker.html");
			templateURL.toAbsolute(_interpreter->getBaseURI());
			templateURL.download(true);
			content = templateURL.getInContent();
		}

		std::cout << content;

		_interpreter->getDataModel().replaceExpressions(content);
		reply.content = content;

		// application/xhtml+xml
		reply.headers["Content-Type"] = "text/html; charset=utf-8";
//		reply.headers["Content-Type"] = "application/xhtml+xml; charset=utf-8";

		// aggressive caching in IE will return all XHR get requests instantenously with the template otherwise
		reply.headers["Cache-Control"] = "no-cache";
//		reply.headers["Cache-Control"] = "max-age=3600";

		HTTPServer::reply(reply);

		// queue invoke request for initial html
		_longPoll.evhttpReq = NULL;
		_outQueue = std::deque<SendRequest>();
		SendRequest sendReq(_invokeReq);
		send(sendReq);

		return true;
	}

	// don't know what to do with other requests
	return false;
}

Data XHTMLInvoker::getDataModelVariables() {
	Data data;
	return data;
}

void XHTMLInvoker::send(const SendRequest& req) {
	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
	SendRequest reqCopy(req);
	_interpreter->getDataModel().replaceExpressions(reqCopy.content);
	Data json = Data::fromJSON(reqCopy.content);
	if (json) {
		reqCopy.data = json;
	}

	if (!_longPoll) {
		_outQueue.push_back(reqCopy);
		return;
	}
	reply(reqCopy, _longPoll);
	_longPoll.evhttpReq = NULL;
}

void XHTMLInvoker::reply(const SendRequest& req, const HTTPServer::Request& longPoll) {
	HTTPServer::Reply reply(longPoll);

	// is there JSON in the content?
	std::string content = req.content;

	if (req.dom) {
		std::stringstream ss;
//		Arabica::DOM::Node<std::string> content = req.dom.getDocumentElement();
		Arabica::DOM::Node<std::string> content = req.dom;
		if (content && iequals(content.getLocalName(), "content")) {
			reply.headers["X-SCXML-Type"] = (HAS_ATTR(content, "type") ? ATTR(content, "type") : "replacechildren");
			reply.headers["X-SCXML-XPath"] = (HAS_ATTR(content, "xpath") ? ATTR(content, "xpath") : "/html/body");
			if (HAS_ATTR(content, "attr"))
				reply.headers["X-SCXML-Attr"] = ATTR(content, "attr");
		}
//		ss << req.getFirstDOMElement();
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

void XHTMLInvoker::cancel(const std::string sendId) {
}

void XHTMLInvoker::invoke(const InvokeRequest& req) {
	_invokeReq = req;
	HTTPServer::registerServlet(_interpreter->getName() + "/" + req.invokeid + ".html", this);
#if __APPLE__
#	if TARGET_OS_IPHONE || TARGET_IPHONE_SIMULATOR
#	else
	// see http://stackoverflow.com/questions/4177744/c-osx-open-default-browser
	CFURLRef url = CFURLCreateWithBytes (
	                   NULL,                        // allocator
	                   (UInt8*)_url.c_str(),     // URLBytes
	                   _url.length(),            // length
	                   kCFStringEncodingASCII,      // encoding
	                   NULL                         // baseURL
	               );
	LSOpenCFURLRef(url,0);
	CFRelease(url);
	return;
#	endif
#endif
#ifdef _WIN32
// see http://support.microsoft.com/kb/224816
	ShellExecute(NULL, "open", _url.c_str(), NULL, NULL, SW_SHOWNORMAL);
	return;
#endif
#ifdef HAS_XDG_OPEN
	std::string systemCmd;
	systemCmd = "xdg-open ";
	systemCmd += _url;
	system(systemCmd.c_str());
	return;
#endif
}

}