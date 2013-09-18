#include "MMISessionManager.h"
#include <uscxml/NameSpacingParser.h>
#include <uscxml/concurrency/tinythread.h>
#include <uscxml/UUID.h>

#include <io/uri.hpp>
#include <glog/logging.h>

namespace uscxml {

using namespace Arabica::DOM;

MMISessionManager::MMISessionManager(Interpreter interpreter) : _protoInterpreter(interpreter) {
	bool success = HTTPServer::registerServlet(interpreter.getName(), this);
	assert(success);
	_factory = new Factory(Factory::getInstance());
	_factory->registerIOProcessor(new MMIIOProcessor(this));
}

MMISessionManager::~MMISessionManager() {
	HTTPServer* httpServer = HTTPServer::getInstance();
	httpServer->unregisterServlet(this);
}

void MMISessionManager::setupHTMLClient(const HTTPServer::Request& req) {
	// open template file
	HTTPServer::Reply reply(req);
	URL templateURL(_protoInterpreter.getBaseURI().asString() + "/templates/mc-html.html");
	templateURL.download(true);
	std::string templateContent = templateURL.getInContent();
	boost::replace_all(templateContent, "${im.url}", _url);
	reply.content = templateContent;
	HTTPServer::reply(reply);
}

bool MMISessionManager::httpRecvRequest(const HTTPServer::Request& req) {
	// is this an initial request from an HTML MC?
	if (!req.data["query"]["token"] && // no token in query
	        !req.data["query"]["context"] && // no context in query
	        boost::iequals(req.data["type"].atom, "get") && // request type is GET
	        boost::icontains(req.data["header"]["Accept"].atom, "text/html") && // accepts html
	        req.content.length() == 0) { // no content
		setupHTMLClient(req);
		return true;
	}

	// is this a comet longpolling request?
	if (boost::iequals(req.data["type"].atom, "get") &&
	        (req.data["query"]["token"] || req.data["query"]["context"])) {
		std::string token = req.data["query"]["token"].atom;
		if (req.data["query"]["token"]) {
			std::string token = req.data["query"]["token"].atom;
			if (_tokens.find(token) != _tokens.end()) {
				MMISessionManager::CometMMISession* comet = static_cast<MMISessionManager::CometMMISession*>(_tokens[token]);
				comet->longPoll(req);
				return true;
			} else {
				LOG(ERROR) << "No session for given token";
			}
		} else if (req.data["query"]["context"]) {
			std::string context = req.data["query"]["context"].atom;
			if (_sessions.find(context) != _sessions.end()) {
				MMISessionManager::CometMMISession* comet = static_cast<MMISessionManager::CometMMISession*>(_sessions[context]);
				comet->longPoll(req);
				return true;
			} else {
				LOG(ERROR) << "No session for given context";
			}
		}
	}

	// assume that there is an mmi event inside
	Document<std::string> mmiDoc = NameSpacingParser::fromXML(req.data.compound.at("content").atom).getDocument();

	if (!mmiDoc) {
		evhttp_send_error(req.curlReq, 204, NULL);
		return true;
	}

	Node<std::string> mmiEvent = MMIEvent::getEventNode(mmiDoc);
	if (!mmiEvent) {
		evhttp_send_error(req.curlReq, 204, NULL);
		return true;
	}

	switch(MMIEvent::getType(mmiEvent)) {
	case MMIEvent::NEWCONTEXTREQUEST: {
		received(NewContextRequest::fromXML(mmiEvent), req.data["query"]["token"].atom);
		evhttp_send_error(req.curlReq, 204, NULL);
		break;
	}
	case MMIEvent::EXTENSIONNOTIFICATION: {
		received(ExtensionNotification::fromXML(mmiEvent));
		evhttp_send_error(req.curlReq, 204, NULL);
		break;
	}
	case MMIEvent::DONENOTIFICATION: {
		received(DoneNotification::fromXML(mmiEvent));
		evhttp_send_error(req.curlReq, 204, NULL);
		break;
	}
	case MMIEvent::STARTRESPONSE: {
		evhttp_send_error(req.curlReq, 204, NULL);
		break;
	}
	default: {
		LOG(ERROR) << "Unknown MMI Event: " << ATTR(mmiEvent, "localName");
		evhttp_send_error(req.curlReq, 204, NULL);
		break;
	}
	}
	return true;
}

void MMISessionManager::received(const ExtensionNotification& mmiEvent) {
	if(_sessions.find(mmiEvent.context) != _sessions.end()) {
		_sessions[mmiEvent.context]->_interpreter.receive(mmiEvent);
	} else {
		LOG(ERROR) << "No session for given context";
	}
}

void MMISessionManager::received(const DoneNotification& mmiEvent) {
	if(_sessions.find(mmiEvent.context) != _sessions.end()) {
		_sessions[mmiEvent.context]->_interpreter.receive(mmiEvent);
	} else {
		LOG(ERROR) << "No session for given context";
	}
}

void MMISessionManager::received(const NewContextRequest& mmiEvent, const std::string& token) {

	// copy DOM from prototype instance
	Arabica::DOM::DOMImplementation<std::string> domFactory = Arabica::SimpleDOM::DOMImplementation<std::string>::getDOMImplementation();
	Arabica::DOM::Document<std::string> newDOM = domFactory.createDocument("", "", 0);
	newDOM.appendChild(newDOM.importNode(_protoInterpreter.getDocument().getDocumentElement(), true));

	// instantiate new interpreter and name it after the context
	std::string contextId = UUID::getUUID();
	Interpreter interpreter = Interpreter::fromDOM(newDOM);
	interpreter.setFactory(_factory);
	interpreter.setName(contextId);
	interpreter.setNameSpaceInfo(_protoInterpreter.getNameSpaceInfo());
	interpreter.setBaseURI(_protoInterpreter.getBaseURI().asString());

	MMISession* session;

	if (token.length() > 0) {
		session = new MMISessionManager::CometMMISession();
		static_cast<MMISessionManager::CometMMISession*>(session)->_token = token;
		_tokens[token] = session;
	} else {
		// todo handle other cases
		session = new MMISessionManager::CometMMISession();
	}
	session->_interpreter = interpreter;

	// save interpreter
	_sessions[contextId] = session;

	interpreter.start();
	interpreter.receive(mmiEvent);

}

void MMISessionManager::received(const NewContextResponse& mmiEvent, const std::string& token) {
	if (_tokens.find(token) != _tokens.end()) {
		_tokens.erase(token);
	}
}

void MMISessionManager::send(const std::string& name, const SendRequest& req) {
	assert(_sessions.find(name) != _sessions.end());
	_sessions[name]->send(req);
}

void MMISessionManager::CometMMISession::send(const SendRequest& req) {
	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
	if (!_longPollingReq) {
		_outQueue.push_back(req);
		return;
	}

	if (req.dom) {
		std::stringstream ss;
		Node<std::string> mmiEvent = MMIEvent::getEventNode(req.dom);
		HTTPServer::Reply reply(_longPollingReq);

		switch (MMIEvent::getType(mmiEvent)) {
		case MMIEvent::NEWCONTEXTRESPONSE: {
			NewContextResponse response = NewContextResponse::fromXML(mmiEvent);
			ss << response.toXML();
			reply.content = ss.str();
			break;
		}
		case MMIEvent::STARTREQUEST: {
			StartRequest request = StartRequest::fromXML(mmiEvent);
			ss << request.toXML();
			reply.content = ss.str();
			break;
		}
		default:
			break;
		}
		reply.headers["Content-Type"] = "application/xml";
		HTTPServer::reply(reply);
		_longPollingReq = HTTPServer::Request();
	}
}

void MMISessionManager::CometMMISession::receive(const Arabica::DOM::Node<std::string>& msg) {

}

void MMISessionManager::CometMMISession::longPoll(const HTTPServer::Request& req) {
	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
	if (_longPollingReq)
		evhttp_send_error(_longPollingReq.curlReq, 204, NULL);
	_longPollingReq = req;
	if (!_outQueue.empty()) {
		send(_outQueue.front());
		_outQueue.pop_front();
	}
}

boost::shared_ptr<IOProcessorImpl> MMISessionManager::MMIIOProcessor::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<IOProcessorImpl> ioProc = boost::shared_ptr<IOProcessorImpl>(new MMISessionManager::MMIIOProcessor(_sessionManager));
	return ioProc;
}

Data MMISessionManager::MMIIOProcessor::getDataModelVariables() {
	Data data;
	return data;
}

void MMISessionManager::MMIIOProcessor::send(const SendRequest& req) {
	SendRequest reqCopy(req);

	if (req.dom) {
		Arabica::DOM::Node<std::string> mmiEvent = MMIEvent::getEventNode(req.dom);
		if (!mmiEvent || !mmiEvent.getNodeType() == Node_base::ELEMENT_NODE)
			return;

		Arabica::DOM::Element<std::string> mmiElem = Arabica::DOM::Element<std::string>(mmiEvent);
		switch (MMIEvent::getType(mmiEvent)) {
		case MMIEvent::STARTRESPONSE:
		case MMIEvent::PREPARERESPONSE:
		case MMIEvent::PAUSERESPONSE:
		case MMIEvent::RESUMERESPONSE:
		case MMIEvent::CANCELRESPONSE:
		case MMIEvent::DONENOTIFICATION:
		case MMIEvent::NEWCONTEXTRESPONSE:
		case MMIEvent::CLEARCONTEXTRESPONSE:
		case MMIEvent::STATUSRESPONSE: {
			// all of the above have a status
			if (!mmiElem.hasAttributeNS(MMIEvent::nameSpace, "Status")) {
				mmiElem.setAttributeNS(MMIEvent::nameSpace, "Status", "Success");
			}
		}
		case MMIEvent::PAUSEREQUEST:
		case MMIEvent::RESUMEREQUEST:
		case MMIEvent::CANCELREQUEST:
		case MMIEvent::CLEARCONTEXTREQUEST:
		case MMIEvent::STATUSREQUEST: {
			// all of the above have a context
			if (!mmiElem.hasAttributeNS(MMIEvent::nameSpace, "Context")) {
				mmiElem.setAttributeNS(MMIEvent::nameSpace, "Context", _interpreter->getName());
			}
		}
		default: {
			if (!mmiElem.hasAttributeNS(MMIEvent::nameSpace, "Source")) {
				mmiElem.setAttributeNS(MMIEvent::nameSpace, "Source", _sessionManager->getURL());
			}
			if (!mmiElem.hasAttributeNS(MMIEvent::nameSpace, "Target")) {
				if (boost::starts_with(_interpreter->getCurrentEvent().name, "mmi.")) {
					mmiElem.setAttributeNS(MMIEvent::nameSpace, "Target", _interpreter->getCurrentEvent().origin);
				}
			}
			if (!mmiElem.hasAttributeNS(MMIEvent::nameSpace, "RequestID")) {
				if (boost::starts_with(_interpreter->getCurrentEvent().name, "mmi.")) {
					mmiElem.setAttributeNS(MMIEvent::nameSpace, "RequestID", _interpreter->getCurrentEvent().sendid);
				}
			}
		}
		}

		if (MMIEvent::getType(mmiEvent) == MMIEvent::EXTENSIONNOTIFICATION && !mmiElem.hasAttribute("Name") && req.name.length() > 0) {
			mmiElem.setAttribute("Name", req.name);
		}
		// use session mgr to dispatch to session

		_sessionManager->send(_interpreter->getName(), reqCopy);
	}

}

}