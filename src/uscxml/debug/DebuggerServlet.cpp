/**
 *  @file
 *  @author     2012-2014 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#include "uscxml/debug/DebuggerServlet.h"
#include "uscxml/debug/DebugSession.h"
#include "uscxml/util/UUID.h"

#include <xercesc/dom/DOMDocument.hpp>
#include <boost/algorithm/string.hpp>

namespace uscxml {

void DebuggerServlet::pushData(std::shared_ptr<DebugSession> session, Data pushData) {
	LOGD(USCXML_DEBUG) << "trying to push " << pushData.at("replyType").atom << std::endl;

	if (!session) {
		if (_sendQueues.size() > 0) // logging is not aware of its interpreter
			_sendQueues.begin()->second.push(pushData);
	} else {
		_sendQueues[session].push(pushData);
	}

	serverPushData(session);
}

void DebuggerServlet::serverPushData(std::shared_ptr<DebugSession> session) {
	if (_sendQueues[session].isEmpty())
		return;

	if (!_clientConns[session])
		return;

	Data reply = _sendQueues[session].pop();
	LOGD(USCXML_DEBUG) << "pushing " << reply.at("replyType").atom << std::endl;
	returnData(_clientConns[session], reply);
	_clientConns[session] = HTTPServer::Request();
}

void DebuggerServlet::returnData(const HTTPServer::Request& request, Data replyData) {
	HTTPServer::Reply reply(request);

	if (!replyData.hasKey("status")) {
		replyData.compound["status"] = Data("success", Data::VERBATIM);
	}

	LOGD(USCXML_DEBUG) << "<- " << replyData << std::endl;

	reply.content = Data::toJSON(replyData);
	reply.headers["Access-Control-Allow-Origin"] = "*";
	reply.headers["Content-Type"] = "application/json";
	HTTPServer::reply(reply);
}

bool DebuggerServlet::isCORS(const HTTPServer::Request& request) {
	return (request.data.at("type").atom == "options" &&
	        request.data.at("header").hasKey("Origin") &&
	        request.data.at("header").hasKey("Access-Control-Request-Method"));
}

void DebuggerServlet::handleCORS(const HTTPServer::Request& request) {
	HTTPServer::Reply corsReply(request);
	if (request.data.at("header").hasKey("Origin")) {
		corsReply.headers["Access-Control-Allow-Origin"] = request.data.at("header").at("Origin").atom;
	} else {
		corsReply.headers["Access-Control-Allow-Origin"] = "*";
	}
	if (request.data.at("header").hasKey("Access-Control-Request-Method"))
		corsReply.headers["Access-Control-Allow-Methods"] = request.data.at("header").at("Access-Control-Request-Method").atom;
	if (request.data.at("header").hasKey("Access-Control-Request-Headers"))
		corsReply.headers["Access-Control-Allow-Headers"] = request.data.at("header").at("Access-Control-Request-Headers").atom;

	//		std::cout << "CORS!" << std::endl << request << std::endl;
	HTTPServer::reply(corsReply);
}

bool DebuggerServlet::requestFromHTTP(const HTTPServer::Request& request) {
	if (!request.data.hasKey("path"))
		return false; //		returnError(request);

	if (isCORS(request)) {
		handleCORS(request);
		return true;
	}

	LOGD(USCXML_DEBUG) << request.data["path"] << ": " << request.data["content"] << std::endl;

	Data replyData;
	// process request that don't need a session
	if (false) {
	} else if (boost::istarts_with(request.data.at("path").atom, "/debug/connect")) {
		processConnect(request);
		return true;
	} else if (boost::starts_with(request.data.at("path").atom, "/debug/sessions")) {
		processListSessions(request);
		return true;
	}

	// get session or return error
	if (false) {
	} else if (!request.data.at("content").hasKey("session")) {
		replyData.compound["status"] = Data("failure", Data::VERBATIM);
		replyData.compound["reason"] = Data("No session given", Data::VERBATIM);
	} else if (_sessionForId.find(request.data.at("content").at("session").atom) == _sessionForId.end()) {
		replyData.compound["status"] = Data("failure", Data::VERBATIM);
		replyData.compound["reason"] = Data("No such session", Data::VERBATIM);
	}
	if (!replyData.empty()) {
		returnData(request, replyData);
		return true;
	}

	std::shared_ptr<DebugSession> session = _sessionForId[request.data.at("content").at("session").atom];

	if (false) {
	} else if (boost::starts_with(request.data.at("path").atom, "/debug/poll")) {
		// save long-standing client poll
		_clientConns[session] = request;
		serverPushData(session);

	} else if (boost::starts_with(request.data.at("path").atom, "/debug/disconnect")) {
		processDisconnect(request);

	} else if (boost::starts_with(request.data.at("path").atom, "/debug/issues")) {
		replyData = session->getIssues();
	} else if (boost::starts_with(request.data.at("path").atom, "/debug/breakpoint/enable/all")) {
		replyData = session->enableAllBreakPoints();
	} else if (boost::starts_with(request.data.at("path").atom, "/debug/breakpoint/disable/all")) {
		replyData = session->disableAllBreakPoints();
	} else if (boost::starts_with(request.data.at("path").atom, "/debug/breakpoint/skipto")) {
		replyData = session->skipToBreakPoint(request.data["content"]);
	} else if (boost::starts_with(request.data.at("path").atom, "/debug/breakpoint/add")) {
		replyData = session->addBreakPoint(request.data["content"]);
	} else if (boost::starts_with(request.data.at("path").atom, "/debug/breakpoint/remove")) {
		replyData = session->removeBreakPoint(request.data["content"]);
	} else if (boost::starts_with(request.data.at("path").atom, "/debug/breakpoint/enable")) {
		replyData = session->enableBreakPoint(request.data["content"]);
	} else if (boost::starts_with(request.data.at("path").atom, "/debug/breakpoint/disable")) {
		replyData = session->disableBreakPoint(request.data["content"]);
	} else if (boost::starts_with(request.data.at("path").atom, "/debug/stop")) {
		replyData = session->debugStop(request.data["content"]);
	} else if (boost::starts_with(request.data.at("path").atom, "/debug/prepare")) {
		replyData = session->debugPrepare(request.data["content"]);
	} else if (boost::starts_with(request.data.at("path").atom, "/debug/attach")) {
		replyData = session->debugAttach(request.data["content"]);
	} else if (boost::starts_with(request.data.at("path").atom, "/debug/start")) {
		replyData = session->debugStart(request.data["content"]);
	} else if (boost::starts_with(request.data.at("path").atom, "/debug/step")) {
		replyData = session->debugStep(request.data["content"]);
	} else if (boost::starts_with(request.data.at("path").atom, "/debug/pause")) {
		replyData = session->debugPause(request.data["content"]);
	} else if (boost::starts_with(request.data.at("path").atom, "/debug/resume")) {
		replyData = session->debugResume(request.data["content"]);
	} else if (boost::starts_with(request.data.at("path").atom, "/debug/eval")) {
		replyData = session->debugEval(request.data["content"]);
	}

	if (!replyData.empty()) {
		returnData(request, replyData);
		return true;
	}

	return true;
}

// someone connected, create a new session
void DebuggerServlet::processConnect(const HTTPServer::Request& request) {
	std::lock_guard<std::recursive_mutex> lock(_mutex);
	std::string sessionId = UUID::getUUID();

	_sessionForId[sessionId] = std::shared_ptr<DebugSession>(new DebugSession());
	_sessionForId[sessionId]->setDebugger(this);

	Data replyData;
	replyData.compound["session"] = Data(sessionId, Data::VERBATIM);
	replyData.compound["status"] = Data("success", Data::VERBATIM);
	returnData(request, replyData);
}

void DebuggerServlet::processDisconnect(const HTTPServer::Request& request) {
	std::lock_guard<std::recursive_mutex> lock(_mutex);

	Data replyData;

	if (!request.data.at("content").hasKey("session")) {
		replyData.compound["status"] = Data("failure", Data::VERBATIM);
		replyData.compound["reason"] = Data("No session given", Data::VERBATIM);
		returnData(request, replyData);
	}

	std::string sessionId = request.data.at("content").at("session").atom;

	if (_sessionForId.find(sessionId) == _sessionForId.end()) {
		replyData.compound["status"] = Data("failure", Data::VERBATIM);
		replyData.compound["reason"] = Data("No such session", Data::VERBATIM);
	} else {
		replyData.compound["status"] = Data("success", Data::VERBATIM);
		detachSession(_sessionForId[sessionId]->getInterpreter().getImpl().get());
		_sessionForId[sessionId]->debugStop(request.data["content"]);
		_clientConns.erase(_sessionForId[sessionId]);
		_sendQueues.erase(_sessionForId[sessionId]);
		_sessionForId.erase(sessionId);
	}

	returnData(request, replyData);
}

void DebuggerServlet::processListSessions(const HTTPServer::Request& request) {
	Data replyData;

	std::map<std::string, std::weak_ptr<InterpreterImpl> > instances = InterpreterImpl::getInstances();
	int index = 0;
	for (auto weakInstance : instances) {

		std::shared_ptr<InterpreterImpl> instance = weakInstance.second.lock();
		if (instance) {
			Data sessionData;
			sessionData.compound["name"] = Data(instance->getName(), Data::VERBATIM);
			sessionData.compound["id"] = Data(instance->getSessionId(), Data::VERBATIM);
			sessionData.compound["source"] = Data(instance->getBaseURL(), Data::VERBATIM);
			sessionData.compound["xml"].node = instance->getDocument();

			replyData.compound["sessions"].array.insert(std::make_pair(index++,sessionData));
		}
	}

	replyData.compound["status"] = Data("success", Data::VERBATIM);
	returnData(request, replyData);
}

/*
void DebuggerServlet::handle(const el::LogDispatchData* data) {
}

void DebuggerServlet::send(google::LogSeverity severity, const char* full_filename,
                       const char* base_filename, int line,
                       const struct ::tm* tm_time,
                       const char* message, size_t message_len) {

// _sendQueue is thread-safe, not sure about ToString though

LogMessage msg(severity,
               full_filename,
               base_filename,
               line,
               tm_time,
               std::string(message, message_len),
               ToString(severity, base_filename, line, tm_time, message, message_len));
msg.compound["replyType"] = Data("log", Data::VERBATIM);
pushData(std::shared_ptr<DebugSession>(), msg);
}
*/

}
