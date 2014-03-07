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
#include "uscxml/UUID.h"
#include <boost/algorithm/string.hpp>

namespace uscxml {

void DebuggerServlet::pushData(Data pushData) {
	std::cout << "trying to push " << pushData["replyType"].atom << std::endl;
	_sendQueue.push(pushData);
	serverPushData();
}

void DebuggerServlet::serverPushData() {
	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
	
	if (_sendQueue.isEmpty())
		return;
	
	if (!_clientConn)
		return;
	
	Data reply = _sendQueue.pop();
	std::cout << "pushing " << reply["replyType"].atom << std::endl;
	returnData(_clientConn, reply);
	_clientConn = HTTPServer::Request();
}

void DebuggerServlet::returnData(const HTTPServer::Request& request, Data replyData) {
	HTTPServer::Reply reply(request);
	
	if (!replyData.hasKey("status")) {
		replyData.compound["status"] = Data("success", Data::VERBATIM);
	}
	
	reply.content = Data::toJSON(replyData);
	reply.headers["Access-Control-Allow-Origin"] = "*";
	reply.headers["Content-Type"] = "application/json";
	HTTPServer::reply(reply);
}
	
void DebuggerServlet::hitBreakpoint(const Interpreter& interpreter,
																		Data data) {
	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);

	data.compound["replyType"] = Data("breakpoint", Data::VERBATIM);
	pushData(data);
	
	_resumeCond.wait(_mutex);
	tthread::this_thread::sleep_for(tthread::chrono::milliseconds(200));
}

bool DebuggerServlet::isCORS(const HTTPServer::Request& request) {
	return (request.data["type"].atom == "options" &&
					request.data["header"].hasKey("Origin") &&
					request.data["header"].hasKey("Access-Control-Request-Method"));
}

void DebuggerServlet::handleCORS(const HTTPServer::Request& request) {
	HTTPServer::Reply corsReply(request);
	if (request.data["header"].hasKey("Origin")) {
		corsReply.headers["Access-Control-Allow-Origin"] = request.data["header"]["Origin"].atom;
	} else {
		corsReply.headers["Access-Control-Allow-Origin"] = "*";
	}
	if (request.data["header"].hasKey("Access-Control-Request-Method"))
		corsReply.headers["Access-Control-Allow-Methods"] = request.data["header"]["Access-Control-Request-Method"].atom;
	if (request.data["header"].hasKey("Access-Control-Request-Headers"))
		corsReply.headers["Access-Control-Allow-Headers"] = request.data["header"]["Access-Control-Request-Headers"].atom;
	
	//		std::cout << "CORS!" << std::endl << request << std::endl;
	HTTPServer::reply(corsReply);
}

bool DebuggerServlet::httpRecvRequest(const HTTPServer::Request& request) {
	if (!request.data.hasKey("path"))
		return false; //		returnError(request);
	
	if (isCORS(request)) {
		handleCORS(request);
		return true;
	}
	
	std::cout << request.data["path"] << ": " << request.data["content"] << std::endl;
	
	if (false) {
	} else if (boost::starts_with(request.data["path"].atom, "/poll")) {
		processPoll(request);
	} else if (boost::starts_with(request.data["path"].atom, "/connect")) {
		processConnect(request);
	} else if (boost::starts_with(request.data["path"].atom, "/disconnect")) {
		processDisconnect(request);
	} else if (boost::starts_with(request.data["path"].atom, "/sessions")) {
		processListSessions(request);
	} else if (boost::starts_with(request.data["path"].atom, "/breakpoint/add")) {
		processAddBreakPoint(request);
	} else if (boost::starts_with(request.data["path"].atom, "/breakpoint/remove")) {
		processRemoveBreakPoint(request);
	} else if (boost::starts_with(request.data["path"].atom, "/debug/prepare")) {
		processDebugPrepare(request);
	} else if (boost::starts_with(request.data["path"].atom, "/debug/start")) {
		processDebugStart(request);
	} else if (boost::starts_with(request.data["path"].atom, "/debug/stop")) {
		processDebugStop(request);
	} else if (boost::starts_with(request.data["path"].atom, "/debug/step")) {
		processDebugStep(request);
	} else if (boost::starts_with(request.data["path"].atom, "/debug/pause")) {
		processDebugPause(request);
	} else if (boost::starts_with(request.data["path"].atom, "/debug/resume")) {
		processDebugResume(request);
	} else if (boost::starts_with(request.data["path"].atom, "/debug/eval")) {
		processDebugEval(request);
	}
		
	return true;
}
	
void DebuggerServlet::processPoll(const HTTPServer::Request& request) {
	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
	_clientConn = request;
	serverPushData();
}

void DebuggerServlet::processDebugPrepare(const HTTPServer::Request& request) {
	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);

//	std::cout << "clearing all pushes" << std::endl;
//	_sendQueue.clear();

	// this will call the destructor if _interpreter already is set
	_resumeCond.notify_all();
	_interpreter = Interpreter::fromXML(request.data["content"].atom);

	Data replyData;
	if (_interpreter) {
		// register ourself as a monitor
		_interpreter.addMonitor(this);
		replyData.compound["status"] = Data("success", Data::VERBATIM);
	} else {
		replyData.compound["status"] = Data("failure", Data::VERBATIM);
	}
	returnData(request, replyData);
}

void DebuggerServlet::processDebugStart(const HTTPServer::Request& request) {
	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
	
	Data replyData;
	if (_interpreter) {
		// register ourself as a monitor
		_interpreter.start();
		replyData.compound["status"] = Data("success", Data::VERBATIM);
	} else {
		replyData.compound["status"] = Data("failure", Data::VERBATIM);
	}
	returnData(request, replyData);
}

void DebuggerServlet::processDebugStop(const HTTPServer::Request& request) {
//		tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);

	stepping(false);

	Data replyData;
	if (_interpreter) {
		_interpreter.stop();
		_resumeCond.notify_all(); // unblock breakpoints
		_interpreter.join();
		_interpreter = Interpreter(); // empty interpreter, calls destructor
		replyData.compound["status"] = Data("success", Data::VERBATIM);
	} else {
		replyData.compound["status"] = Data("failure", Data::VERBATIM);
		replyData.compound["reason"] = Data("Interpreter already stopped", Data::VERBATIM);
	}
	returnData(request, replyData);
}

void DebuggerServlet::processDebugEval(const HTTPServer::Request& request) {
	Data replyData;
	if (!_interpreter) {
		replyData.compound["status"] = Data("failure", Data::VERBATIM);
		replyData.compound["reason"] = Data("No interpreter running", Data::VERBATIM);
	} else if (!_interpreter.getDataModel()) {
		replyData.compound["status"] = Data("failure", Data::VERBATIM);
		replyData.compound["reason"] = Data("No datamodel available", Data::VERBATIM);
	} else if (!request.data["content"].hasKey("expression")) {
		replyData.compound["status"] = Data("failure", Data::VERBATIM);
		replyData.compound["reason"] = Data("No expression given", Data::VERBATIM);
	} else {
		std::string expr = request.data["content"]["expression"].atom;
		try {
			replyData.compound["eval"] = _interpreter.getDataModel().getStringAsData(expr);
		} catch (Event e) {
			replyData.compound["eval"] = e.data;
			replyData.compound["eval"].compound["error"] = Data(e.name, Data::VERBATIM);
		}
		replyData.compound["status"] = Data("success", Data::VERBATIM);
	}
	returnData(request, replyData);
}

void DebuggerServlet::processDebugStep(const HTTPServer::Request& request) {
	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);

	stepping(true);
	_resumeCond.notify_one();
	
	Data replyData;
	if (_interpreter && !_interpreter.isRunning()) {
		// register ourself as a monitor
		_interpreter.start();
		replyData.compound["status"] = Data("success", Data::VERBATIM);
	} else {
		replyData.compound["status"] = Data("failure", Data::VERBATIM);
	}
	returnData(request, replyData);
	
}

void DebuggerServlet::processDebugResume(const HTTPServer::Request& request) {
	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
	
	stepping(false);

	Data replyData;
	replyData.compound["status"] = Data("success", Data::VERBATIM);
	returnData(request, replyData);

	_resumeCond.notify_one();
}

void DebuggerServlet::processDebugPause(const HTTPServer::Request& request) {
	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
	
	Data replyData;
	replyData.compound["status"] = Data("success", Data::VERBATIM);
	returnData(request, replyData);
}

void DebuggerServlet::processConnect(const HTTPServer::Request& request) {
	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
	_sessionId = UUID::getUUID();
	_breakPoints.clear();
//	_sendQueue.clear();
	
	Data replyData;
	replyData.compound["session"] = Data(_sessionId, Data::VERBATIM);
	replyData.compound["status"] = Data("success", Data::VERBATIM);
	returnData(request, replyData);
}

void DebuggerServlet::processListSessions(const HTTPServer::Request& request) {
	Data replyData;
	
	// TODO: return actual data
	Data sessionData;
	sessionData.compound["name"] = Data("Not actually a Session", Data::VERBATIM);
	sessionData.compound["id"] = Data("23452523-wg23g2g2-234t2g-23g2g", Data::VERBATIM);
	replyData.compound["sessions"].array.push_back(sessionData);
	
	sessionData.compound["name"] = Data("But returned from the server!", Data::VERBATIM);
	sessionData.compound["id"] = Data("swfgsgfw-g232vqvq-234t2g-23g2g", Data::VERBATIM);
	replyData.compound["sessions"].array.push_back(sessionData);
	
	replyData.compound["status"] = Data("success", Data::VERBATIM);
	returnData(request, replyData);
}

void DebuggerServlet::processDisconnect(const HTTPServer::Request& request) {
	Data replyData;
	replyData.compound["status"] = Data("success", Data::VERBATIM);
	returnData(request, replyData);
}

void DebuggerServlet::processAddBreakPoint(const HTTPServer::Request& request) {
	Breakpoint breakPoint(request.data["content"]);
	Data replyData;
	if (breakPoint.isValid()) {
		replyData.compound["status"] = Data("success", Data::VERBATIM);

		if (_breakPoints.find(breakPoint) == _breakPoints.end()) {
			_breakPoints.insert(breakPoint);
		}
	} else {
		replyData.compound["status"] = Data("failure", Data::VERBATIM);
	}
	returnData(request, replyData);
}

void DebuggerServlet::processRemoveBreakPoint(const HTTPServer::Request& request) {
	Breakpoint breakPoint(request.data["content"]);
	Data replyData;
	if (_breakPoints.erase(breakPoint) > 0) {
		replyData.compound["status"] = Data("success", Data::VERBATIM);
	} else {
		replyData.compound["message"] = Data("No such breakpoint", Data::VERBATIM);
		replyData.compound["status"] = Data("failure", Data::VERBATIM);
	}
	returnData(request, replyData);
}


}