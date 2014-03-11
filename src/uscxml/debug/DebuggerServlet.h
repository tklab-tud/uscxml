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

#ifndef DEBUGGERSERVLET_H_ATUMDA3G
#define DEBUGGERSERVLET_H_ATUMDA3G

#include "uscxml/Common.h"
#include "getopt.h"
#include <glog/logging.h>

#include "uscxml/server/HTTPServer.h"
#include "uscxml/Interpreter.h"

#include "uscxml/debug/Debugger.h"
#include "uscxml/concurrency/tinythread.h"

namespace uscxml {

class USCXML_API DebuggerServlet : public Debugger, public HTTPServlet, public google::LogSink {
public:
	class LogMessage : public Data {
	public:
		LogMessage(google::LogSeverity severity, const char* full_filename,
							 const char* base_filename, int line,
							 const struct ::tm* tm_time,
							 std::string message, std::string formatted) {
			
			compound["severity"] = severity;
			compound["fullFilename"] = Data(full_filename, Data::VERBATIM);
			compound["baseFilename"] = Data(base_filename, Data::VERBATIM);
			compound["line"] = line;
			compound["message"] = Data(message, Data::VERBATIM);
			compound["time"] = Data(mktime((struct ::tm*)tm_time), Data::INTERPRETED);
			compound["formatted"] = Data(formatted, Data::VERBATIM);
		}
	};
	
	virtual ~DebuggerServlet() {}
	
	// from Debugger
	virtual void addBreakpoint(const Breakpoint& breakpoint) {};

	bool isCORS(const HTTPServer::Request& request);
	void handleCORS(const HTTPServer::Request& request);

	bool httpRecvRequest(const HTTPServer::Request& request);
	void setURL(const std::string& url) {
		_url = url;
	}

	void pushData(boost::shared_ptr<DebugSession> session, Data pushData);
	void returnData(const HTTPServer::Request& request, Data replyData);

	void processDisconnect(const HTTPServer::Request& request);
	void processConnect(const HTTPServer::Request& request);
	void processListSessions(const HTTPServer::Request& request);

//	void processDebugPrepare(const HTTPServer::Request& request);
//	void processDebugAttach(const HTTPServer::Request& request);
//	void processDebugStart(const HTTPServer::Request& request);
//	void processDebugStop(const HTTPServer::Request& request);

//	void processDebugEval(const HTTPServer::Request& request);
//	void processDebugStart(const HTTPServer::Request& request);
//	void processDebugStop(const HTTPServer::Request& request);
//	void processDebugStep(const HTTPServer::Request& request);
//	void processDebugResume(const HTTPServer::Request& request);
//	void processDebugPause(const HTTPServer::Request& request);
//	void processAddBreakPoint(const HTTPServer::Request& request);
//	void processRemoveBreakPoint(const HTTPServer::Request& request);
//	void processPoll(const HTTPServer::Request& request);
  
	// Logsink
	virtual void send(google::LogSeverity severity, const char* full_filename,
										const char* base_filename, int line,
										const struct ::tm* tm_time,
										const char* message, size_t message_len);

protected:
	void serverPushData(boost::shared_ptr<DebugSession>);

	std::string _url;
	std::map<boost::shared_ptr<DebugSession>, HTTPServer::Request> _clientConns;
  std::map<boost::shared_ptr<DebugSession>, concurrency::BlockingQueue<Data> > _sendQueues;
  std::map<std::string, boost::shared_ptr<DebugSession> > _sessionForId;

	tthread::recursive_mutex _mutex;
};

}

#endif /* end of include guard: DEBUGGERSERVLET_H_ATUMDA3G */
