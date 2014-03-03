#include "uscxml/config.h"
#include "uscxml/Interpreter.h"
#include "uscxml/DOMUtils.h"
#include "uscxml/UUID.h"
#include "uscxml/debug/SCXMLDotWriter.h"
#include <glog/logging.h>
#include <time.h> // mktime

#include <boost/algorithm/string.hpp>

#ifdef HAS_SIGNAL_H
#include <signal.h>
#endif

#ifdef HAS_EXECINFO_H
#include <execinfo.h>
#endif

#ifdef HAS_DLFCN_H
#include <dlfcn.h>
#endif

using namespace uscxml;

class Debugger : public HTTPServlet, public InterpreterMonitor, public google::LogSink {
public:
	class BreakPoint {
	public:

		enum When {
			UNDEF_WHEN, AFTER, BEFORE, ON
		};

		enum Subject {
			UNDEF_SUBJECT, STATE, TRANSITION, CONFIGURATION, EVENT
		};

		enum Action {
			UNDEF_ACTION, ENTER, EXIT
		};

		BreakPoint(const Data& data) {
			subject = UNDEF_SUBJECT;
			when    = UNDEF_WHEN;
			action  = UNDEF_ACTION;
			
			if (data.hasKey("action")) {
				if (false) {
				} else if (iequals(data["action"], "enter")) {
					action = ENTER;
				} else if (iequals(data["action"], "exit")) {
					action = EXIT;
				}
			}
			if (data.hasKey("time")) {
				if (false) {
				} else if (iequals(data["time"], "before")) {
					when = BEFORE;
				} else if (iequals(data["time"], "after")) {
					when = AFTER;
				} else if (iequals(data["time"], "on")) {
					when = ON;
				}
			}
			if (data.hasKey("subject")) {
				if (false) {
				} else if (iequals(data["subject"], "state")) {
					subject = STATE;
					if (data.hasKey("stateId"))
						state = data["stateId"].atom;
				} else if (iequals(data["subject"], "transition")) {
					subject = TRANSITION;
					if (data.hasKey("fromStateId"))
						fromState = data["fromStateId"].atom;
					if (data.hasKey("toStateId"))
						fromState = data["toStateId"].atom;
				} else if (iequals(data["subject"], "event")) {
					subject = EVENT;
					if (data.hasKey("eventName"))
						eventName = data["eventName"].atom;
				} else if (iequals(data["subject"], "configuration")) {
					subject = CONFIGURATION;
				} else if (iequals(data["subject"], "microstep")) {
					subject = CONFIGURATION;
				}
			}

			if (data.hasKey("condition")) {
				condition = data["condition"].atom;
			}
		}
		
		bool isValid() {
			return true;
		}
		
	protected:
		When when;
		Subject subject;
		Action action;
		
		std::string state;
		std::string toState;
		std::string fromState;
		std::string eventName;
		
		std::string condition;
		
	};
	
	class LogMessage {
	public:
		google::LogSeverity severity;
		std::string full_filename;
		std::string base_filename;
		int line;
		const struct ::tm* tm_time;
		std::string message;
		std::string formatted;
		
		Data toData() {
			Data data;
			data.compound["severity"] = severity;
			data.compound["fullFilename"] = Data(full_filename, Data::VERBATIM);
			data.compound["baseFilename"] = Data(base_filename, Data::VERBATIM);
			data.compound["line"] = line;
			data.compound["message"] = Data(message, Data::VERBATIM);
			data.compound["time"] = mktime((struct ::tm*)tm_time);
			data.compound["formatted"] = Data(formatted, Data::VERBATIM);
			return data;
		}
	};

	std::string _url;
	Interpreter _interpreter;
	HTTPServer::Request _debugReq;
	tthread::recursive_mutex _mutex;
	std::list<LogMessage> _logMessages;
	std::map<std::string, BreakPoint> _breakPoints;
	
	virtual ~Debugger() {
	}
	
	// callbacks from http requests
	
	void debug(const HTTPServer::Request& request) {
		tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);

		// save request and run until we reach a breakpoint
		_debugReq = request;
		_interpreter.interpret();
	}
	
	void connect(const HTTPServer::Request& request) {
		Data replyData;
		replyData.compound["status"] = Data("success", Data::VERBATIM);
		returnData(request, replyData);
	}

	void disconnect(const HTTPServer::Request& request) {
		Data replyData;
		replyData.compound["status"] = Data("success", Data::VERBATIM);
		returnData(request, replyData);
	}

	void prepare(const HTTPServer::Request& request) {
		tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);

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

	void addBreakPoint(const HTTPServer::Request& request) {
		BreakPoint breakPoint(request.data["content"]);
		Data replyData;
		if (breakPoint.isValid()) {
			replyData.compound["status"] = Data("success", Data::VERBATIM);
		} else {
			replyData.compound["status"] = Data("failure", Data::VERBATIM);
		}
		returnData(request, replyData);
	}
	
	// helpers
	
	void returnData(const HTTPServer::Request& request, Data replyData) {
		//always include latest log
		while(_logMessages.size() > 0) {
			replyData.compound["log"].array.push_back(_logMessages.front().toData());
			_logMessages.pop_front();
		}

		HTTPServer::Reply reply(request);
		reply.headers["Content-type"] = "application/json";
		reply.headers["Access-Control-Allow-Origin"] = "*";
		reply.content = Data::toJSON(replyData);
		HTTPServer::reply(reply);
	}
	
	bool isCORS(const HTTPServer::Request& request) {
		return (request.data["type"].atom == "options" &&
						request.data["header"].hasKey("Origin") &&
						request.data["header"].hasKey("Access-Control-Request-Method"));
	}
	
	void handleCORS(const HTTPServer::Request& request) {
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
	
	// HTTPServlet
	
	bool httpRecvRequest(const HTTPServer::Request& request) {
		if (isCORS(request)) {
			handleCORS(request);
			return true;
		}
		
		std::cout << Data::toJSON(request.data) << std::endl;
		
		if (false) {
		} else if (boost::istarts_with(request.data["path"].atom, "/connect")) {
			connect(request);
		} else if (boost::istarts_with(request.data["path"].atom, "/disconnect")) {
			disconnect(request);
		} else if (boost::istarts_with(request.data["path"].atom, "/prepare")) {
			prepare(request);
		} else if (boost::istarts_with(request.data["path"].atom, "/debug")) {
			debug(request);
		} else if (boost::istarts_with(request.data["path"].atom, "/breakpoint/add")) {
			addBreakPoint(request);
		}
		return true;
	}
	void setURL(const std::string& url) {
		_url = url;
	}
		
	// InterpreterMonitor
	void onStableConfiguration(Interpreter interpreter) {
	}
	
	void beforeCompletion(Interpreter interpreter) {}
	void afterCompletion(Interpreter interpreter) {}
	void beforeMicroStep(Interpreter interpreter) {}
	void beforeTakingTransitions(Interpreter interpreter, const Arabica::XPath::NodeSet<std::string>& transitions) {}
	void beforeEnteringStates(Interpreter interpreter, const Arabica::XPath::NodeSet<std::string>& statesToEnter) {}
	void afterEnteringStates(Interpreter interpreter) {}
	void beforeExitingStates(Interpreter interpreter, const Arabica::XPath::NodeSet<std::string>& statesToExit) {}
	void afterExitingStates(Interpreter interpreter) {}

	// google::LogSink
	
  virtual void send(google::LogSeverity severity, const char* full_filename,
                    const char* base_filename, int line,
                    const struct ::tm* tm_time,
                    const char* message, size_t message_len) {
		
		tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);

		LogMessage msg;
		msg.severity = severity;
		msg.full_filename = full_filename;
		msg.base_filename = base_filename;
		msg.line = line;
		msg.tm_time = tm_time;
		msg.message = std::string(message, message_len);
		msg.formatted = ToString(severity, base_filename, line, tm_time, message, message_len);
		
		_logMessages.push_back(msg);
	}
		
};


int main(int argc, char** argv) {
	using namespace uscxml;

	InterpreterOptions options = InterpreterOptions::fromCmdLine(argc, argv);
	Debugger debugger;

	// setup logging
	google::InitGoogleLogging(argv[0]);
	google::AddLogSink(&debugger);

	// setup HTTP server
	HTTPServer::getInstance(18088, 18089, NULL);


	HTTPServer::getInstance()->registerServlet("/", &debugger);

	while(true)
		tthread::this_thread::sleep_for(tthread::chrono::seconds(1));
	
	
	return EXIT_SUCCESS;
}