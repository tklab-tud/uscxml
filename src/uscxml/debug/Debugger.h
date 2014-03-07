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

#ifndef DEBUGGERMONITOR_H_Z050WPFH
#define DEBUGGERMONITOR_H_Z050WPFH

#include "uscxml/Message.h"
#include "uscxml/Interpreter.h"
#include "uscxml/debug/Breakpoint.h"

#include <glog/logging.h>
	
namespace uscxml {
	
class USCXML_API Debugger : public InterpreterMonitor, public google::LogSink {
public:
	Debugger() {
		_isStepping = false;
	}
	virtual ~Debugger() {}

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
  
	virtual void pushData(Data pushData) = 0;
	virtual void hitBreakpoint(const Interpreter& interpreter, Data data) = 0;
	
	void stepping(bool enable) {
		_isStepping = enable;
	}
	
	// InterpreterMonitor
	virtual void beforeProcessingEvent(Interpreter interpreter, const Event& event);
	virtual void beforeMicroStep(Interpreter interpreter);
	virtual void beforeExitingState(Interpreter interpreter, const Arabica::DOM::Element<std::string>& state);
	virtual void afterExitingState(Interpreter interpreter, const Arabica::DOM::Element<std::string>& state);
	virtual void beforeUninvoking(Interpreter interpreter, const Arabica::DOM::Element<std::string>& invokeElem, const std::string& invokeid);
	virtual void afterUninvoking(Interpreter interpreter, const Arabica::DOM::Element<std::string>& invokeElem, const std::string& invokeid);
	virtual void beforeTakingTransition(Interpreter interpreter, const Arabica::DOM::Element<std::string>& transition);
	virtual void afterTakingTransition(Interpreter interpreter, const Arabica::DOM::Element<std::string>& transition);
	virtual void beforeEnteringState(Interpreter interpreter, const Arabica::DOM::Element<std::string>& state);
	virtual void afterEnteringState(Interpreter interpreter, const Arabica::DOM::Element<std::string>& state);
	virtual void beforeInvoking(Interpreter interpreter, const Arabica::DOM::Element<std::string>& invokeElem, const std::string& invokeid);
	virtual void afterInvoking(Interpreter interpreter, const Arabica::DOM::Element<std::string>& invokeElem, const std::string& invokeid);
	virtual void afterMicroStep(Interpreter interpreter);
	virtual void beforeExecutingContent(Interpreter interpreter, const Arabica::DOM::Element<std::string>& element) {}
	virtual void afterExecutingContent(Interpreter interpreter, const Arabica::DOM::Element<std::string>& element) {}
	virtual void onStableConfiguration(Interpreter interpreter);
	virtual void beforeCompletion(Interpreter interpreter) {}
	virtual void afterCompletion(Interpreter interpreter);

	// Logsink
	virtual void send(google::LogSeverity severity, const char* full_filename,
										const char* base_filename, int line,
										const struct ::tm* tm_time,
										const char* message, size_t message_len);

protected:
  
	void handleTransition(Interpreter interpreter,
												const Arabica::DOM::Element<std::string>& transition,
												Breakpoint::When when);
	void handleState(Interpreter interpreter,
									 const Arabica::DOM::Element<std::string>& state,
									 Breakpoint::When when,
									 Breakpoint::Action action);
	void handleInvoke(Interpreter interpreter,
										const Arabica::DOM::Element<std::string>& invokeElem,
										const std::string& invokeId,
										Breakpoint::When when,
										Breakpoint::Action action);
	void handleStable(Interpreter interpreter, Breakpoint::When when);
	void handleMicrostep(Interpreter interpreter, Breakpoint::When when);
	void handleEvent(Interpreter interpreter, const Event& event, Breakpoint::When when);
	void checkBreakpoints(Interpreter interpreter, const std::list<Breakpoint> qualifiedBreakpoints);

	bool _isStepping;
	std::set<Breakpoint> _breakPoints;
  
};

}


#endif /* end of include guard: DEBUGGERMONITOR_H_Z050WPFH */
