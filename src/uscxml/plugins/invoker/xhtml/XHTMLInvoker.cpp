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
#include "uscxml/dom/DOMUtils.h"
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
	HTTPServer::unregisterServlet(this);
};

boost::shared_ptr<InvokerImpl> XHTMLInvoker::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<XHTMLInvoker> invoker = boost::shared_ptr<XHTMLInvoker>(new XHTMLInvoker());
	invoker->_interpreter = interpreter;
	return invoker;
}

bool XHTMLInvoker::httpRecvRequest(const HTTPServer::Request& req) {
	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);

	// these are the XHR requests
	if (iequals(req.data.at("header").at("X-Requested-With").atom, "XMLHttpRequest")) {
		if (iequals(req.data.at("type").atom, "get")) {
			// this is the incoming the long-polling GET
			if (_longPoll) {
				// cancel old longPoller
				evhttp_send_error(_longPoll.evhttpReq, 204, NULL);
				_longPoll.evhttpReq = NULL;
			}

			_longPoll = req;
			if (!_outQueue.empty()) {
				// do we have some send requests pending?
				HTTPServer::Reply reply =_outQueue.front();
				reply.setRequest(_longPoll);
				HTTPServer::reply(reply);
				_outQueue.pop_front();
				_longPoll.evhttpReq = NULL;
			}
			return true;

		} else {
			// an incomping event per POST request
			Event ev(req);
			if (ev.data["header"].hasKey("X-SCXML-Name")) {
				ev.name = ev.data["header"]["X-SCXML-Name"].atom;
			} else {
				ev.name = req.data.at("type").atom;
			}

			// initialize data
			ev.data = req.data.at("content");
			ev.eventType = Event::EXTERNAL;

			HTTPServer::Reply reply(req);
			HTTPServer::reply(reply);

			returnEvent(ev);
			return true;
		}
	}

	// initial request for a document
	if (!req.data.hasKey("query") && // no query parameters
	        iequals(req.data.at("type").atom, "get") && // request type is GET
	        req.content.length() == 0) { // no content

		// send template to establish long polling
		HTTPServer::Reply reply(req);

		// _invokeReq.content will contain the actual content as we needed to replace expressions in the interpreter thread

		if (!_invokeReq.data.empty()) {
			// just reply with given data as json, this time and for ever
			reply.content = _invokeReq.content;
			reply.headers["Content-type"] = "application/json";
			HTTPServer::reply(reply);
			return true;

		} else if (_invokeReq.dom) {
			// there is some XML given with the content
			if (HAS_ATTR_CAST(_invokeReq.dom, "type")) {
				// it's special XML to send per Comet later on, default to sending template and enqueue
				_longPoll.evhttpReq = NULL;
				_outQueue = std::deque<HTTPServer::Reply>();

				HTTPServer::Reply reply;
				reply.content = _invokeReq.content;
				reply.headers["Content-type"] = "application/xml";
				_outQueue.push_back(reply);

				// no return here - we wan to send the template below

			} else {
				// it's plain XML now and forever
				reply.content = _invokeReq.content;
				reply.headers["Content-type"] = "application/xml";
				HTTPServer::reply(reply);
				return true;
			}
		} else if (_invokeReq.content.size() > 0) {

			// just reply as text this time and for ever
			reply.content = _invokeReq.content;
			reply.headers["Content-type"] = "text/plain";
			HTTPServer::reply(reply);
			return true;
		}

		/*
		 * Return our template to establish a two way communication via comet
		 * If we want to replace expressions in the temaplte, we have to do it in invoke()
		 * for thread safety of the datamodel.
		 */

		// this file is generated from template/xhtml-invoker.xhtml via xxd
#include "template/xhtml-invoker.inc.h"

		// aggressive caching in IE will return all XHR get requests instantenously otherwise
		reply.headers["Cache-Control"] = "no-cache";
		reply.headers["Content-Type"] = "text/html; charset=utf-8";

		reply.content = std::string((const char*)template_xhtml_invoker_html, template_xhtml_invoker_html_len);
		HTTPServer::reply(reply);
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

	HTTPServer::Reply reply;

	if (req.dom) {
		// XML
		std::stringstream ss;
		if (req.dom.getNodeType() == Arabica::DOM::Node_base::ELEMENT_NODE) {
			Arabica::DOM::Element<std::string> contentElem = Arabica::DOM::Element<std::string>(req.dom);

			if (HAS_ATTR(contentElem, "type"))
				reply.headers["X-SCXML-Type"] = ATTR(contentElem, "type");
			if (HAS_ATTR(contentElem, "xpath"))
				reply.headers["X-SCXML-XPath"] = ATTR(contentElem, "xpath");
			if (HAS_ATTR(contentElem, "attr"))
				reply.headers["X-SCXML-Attr"] = ATTR(contentElem, "attr");
		}

		ss << req.dom;
		reply.content = ss.str();
		reply.headers["Content-Type"] = "application/xml";

	} else if (!req.data.empty()) {
		// JSON
		reply.content = Data::toJSON(req.data);
		reply.headers["Content-Type"] = "application/json";
	} else if (req.content.length() > 0) {
		reply.content = req.content;
		reply.headers["Content-Type"] = "text/plain";
	}

	// TODO: Params to set variables?

	_interpreter->getDataModel().replaceExpressions(reply.content);

	if (!_longPoll) {
		_outQueue.push_back(reply);
		return;
	}
	reply.setRequest(_longPoll);
	HTTPServer::reply(reply);
	_longPoll.evhttpReq = NULL;
}

void XHTMLInvoker::cancel(const std::string sendId) {
	HTTPServer::unregisterServlet(this);
}

void XHTMLInvoker::invoke(const InvokeRequest& req) {
	_invokeReq = req;

	// make sure _invokeReq.content contains correct and substituted string
	if (!_invokeReq.data.empty()) {
		_invokeReq.content = Data::toJSON(_invokeReq.data);
	} else if (_invokeReq.dom) {
		std::stringstream ss;
		ss << _invokeReq.dom;
		_invokeReq.content = ss.str();
	}
	_interpreter->getDataModel().replaceExpressions(_invokeReq.content);

	std::string browserURL;
	if (req.src.size() > 0) {
		// no src given, send browser off to some remote url
		browserURL = req.src;
	} else {
		// invoke to talk to us
		HTTPServer::registerServlet(_interpreter->getName() + "/" + req.invokeid + ".html", this);
		if (_url.size() == 0) {
			returnErrorExecution("No HTTP server running");
		}
		browserURL = _url.c_str();
	}
#if __APPLE__
#	if TARGET_OS_IPHONE || TARGET_IPHONE_SIMULATOR
#	else
	// see http://stackoverflow.com/questions/4177744/c-osx-open-default-browser
	CFURLRef url = CFURLCreateWithBytes (
	                   NULL,                        // allocator
	                   (UInt8*)browserURL.c_str(),     // URLBytes
	                   browserURL.length(),            // length
	                   kCFStringEncodingASCII,      // encoding
	                   NULL                         // baseURL
	               );
	if (LSOpenCFURLRef(url,0) == errSecSuccess) {
		if (url)
			CFRelease(url);
		return;
	}
#	endif
#endif
#ifdef _WIN32
// see http://support.microsoft.com/kb/224816
	ShellExecute(NULL, "open", browserURL.c_str(), NULL, NULL, SW_SHOWNORMAL);
	return;
#endif
#ifdef HAS_XDG_OPEN
	std::string systemCmd;
	systemCmd = "xdg-open ";
	systemCmd += browserURL;
	if (system(systemCmd.c_str()) >= 0)
		return;
#endif
	LOG(ERROR) << "Could not open a HTML browser, access '" << browserURL << "' yourself.";
}

}