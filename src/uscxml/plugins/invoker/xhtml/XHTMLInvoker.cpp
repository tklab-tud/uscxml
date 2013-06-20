#include <uscxml/config.h>
#include "XHTMLInvoker.h"
#include <glog/logging.h>
#include <uscxml/plugins/ioprocessor/comet/CometIOProcessor.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

#if defined(__APPLE__) and defined(TARGET_OS_MAC)
#include <CoreFoundation/CFBundle.h>
#include <ApplicationServices/ApplicationServices.h>
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool connect(pluma::Host& host) {
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
	if (boost::iequals(req.data["header"]["X-Requested-With"].atom, "XMLHttpRequest")) {
		if (boost::iequals(req.data["type"].atom, "get")) {
			if (_longPoll) {
				evhttp_send_error(_longPoll.curlReq, 204, NULL);
				_longPoll.curlReq = NULL;
			}
			_longPoll = req;
			if (!_outQueue.empty()) {
				send(_outQueue.front());
				_outQueue.pop_front();
			}
			return true;
		} else {
			Event ev(req);
			if (ev.data["header"]["X-SCXML-Name"]) {
				ev.name = ev.data["header"]["X-SCXML-Name"].atom;
			}
			ev.origin = _invokeId;
			ev.initContent(req.data["content"].atom);
			ev.data.compound["Connection"] = req.data;
			// content is already on ev.raw
			ev.data.compound["Connection"].compound.erase("content");

			returnEvent(ev);
			return true;
		}
	}

	// initial request for a document
	if (!req.data["query"] && // no query parameters
	        boost::iequals(req.data["type"].atom, "get") && // request type is GET
	        (boost::icontains(req.data["header"]["Accept"].atom, "text/html") ||  // accepts html or
	         boost::contains(req.data["header"]["User-Agent"].atom, "MSIE")) && // is the internet explorer
	        req.content.length() == 0) { // no content

		HTTPServer::Reply reply(req);
		URL templateURL("templates/xhtml-invoker.html");
		templateURL.toAbsolute(_interpreter->getBaseURI());
		templateURL.download(true);
		std::string templateContent = templateURL.getInContent();
		boost::replace_all(templateContent, "${scxml.server}", _url);
		boost::replace_all(templateContent, "${scxml.invokeId}", _invokeId);

		std::string content;
		std::stringstream ss;
		if (_invokeReq.dom) {
			ss << _invokeReq.getFirstDOMElement();
			content = ss.str();
		} else if(_invokeReq.data) {
			ss << _invokeReq.data;
			content = ss.str();
		} else {
			content = _invokeReq.content;
		}
		boost::replace_all(templateContent, "${scxml.content}", content);
		reply.content = templateContent;
		reply.headers["Content-Type"] = "text/html";

		// aggressive caching in IE will return all XHR get requests instantenously with the template otherwise
		reply.headers["Cache-Control"] = "no-cache";

		HTTPServer::reply(reply);

		// queue invoke request for initial html
		_longPoll.curlReq = NULL;
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
	if (!_longPoll) {
		_outQueue.push_back(req);
		return;
	}
	reply(req, _longPoll);
	_longPoll.curlReq = NULL;
}

void XHTMLInvoker::reply(const SendRequest& req, const HTTPServer::Request& longPoll) {
	HTTPServer::Reply reply(longPoll);

	if (req.dom) {
		std::stringstream ss;
		Arabica::DOM::Node<std::string> content = req.dom.getDocumentElement();
		if (content && boost::iequals(content.getLocalName(), "content")) {
			reply.headers["X-SCXML-Type"] = (HAS_ATTR(content, "type") ? ATTR(content, "type") : "replacechildren");
			reply.headers["X-SCXML-XPath"] = (HAS_ATTR(content, "xpath") ? ATTR(content, "xpath") : "/html/body");
			if (HAS_ATTR(content, "attr"))
				reply.headers["X-SCXML-Attr"] = ATTR(content, "attr");
		}
		ss << req.getFirstDOMElement();
		reply.content = ss.str();
		reply.headers["Content-Type"] = "application/xml";
	} else if (req.data) {
		reply.content = Data::toJSON(req.data);
		reply.headers["Content-Type"] = "application/json";
	} else if (req.content.length() > 0) {
		reply.content = req.content;
		reply.headers["Content-Type"] = "application/text";
	}

	if (req.params.find("Content-Type") != req.params.end())
		reply.headers["Content-Type"] = req.params.find("Content-Type")->first;

	HTTPServer::reply(reply);
}

void XHTMLInvoker::cancel(const std::string sendId) {
}

void XHTMLInvoker::invoke(const InvokeRequest& req) {
	_invokeReq = req;
	HTTPServer::registerServlet(_interpreter->getName() + "/xhtml/" + req.invokeid, this);
#if defined(__APPLE__) and defined(TARGET_OS_MAC)
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