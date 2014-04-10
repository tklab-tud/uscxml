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
#include "uscxml/debug/DebugSession.h"
	
namespace uscxml {
	
class USCXML_API Debugger : public InterpreterMonitor {
public:
	Debugger() {
	}
	virtual ~Debugger() {}
  
	virtual void attachSession(Interpreter interpreter, boost::shared_ptr<DebugSession> session) {
		tthread::lock_guard<tthread::recursive_mutex> lock(_sessionMutex);
		_sessionForInterpreter[interpreter] = session;
	}

	virtual void detachSession(Interpreter interpreter) {
		tthread::lock_guard<tthread::recursive_mutex> lock(_sessionMutex);
		_sessionForInterpreter.erase(interpreter);
	}
	
	virtual boost::shared_ptr<DebugSession> getSession(Interpreter interpreter) {
		tthread::lock_guard<tthread::recursive_mutex> lock(_sessionMutex);
		if (_sessionForInterpreter.find(interpreter) != _sessionForInterpreter.end())
			return _sessionForInterpreter[interpreter];
		return boost::shared_ptr<DebugSession>();
	}
	
	virtual void pushData(boost::shared_ptr<DebugSession> session, Data pushData) = 0;
		
	// InterpreterMonitor
	virtual void beforeProcessingEvent(Interpreter interpreter, const Event& event);
	virtual void beforeMicroStep(Interpreter interpreter);
	virtual void beforeExitingState(Interpreter interpreter, const Arabica::DOM::Element<std::string>& state, bool moreComing);
	virtual void afterExitingState(Interpreter interpreter, const Arabica::DOM::Element<std::string>& state, bool moreComing);
	virtual void beforeExecutingContent(Interpreter interpreter, const Arabica::DOM::Element<std::string>& element);
	virtual void afterExecutingContent(Interpreter interpreter, const Arabica::DOM::Element<std::string>& element);
	virtual void beforeUninvoking(Interpreter interpreter, const Arabica::DOM::Element<std::string>& invokeElem, const std::string& invokeid);
	virtual void afterUninvoking(Interpreter interpreter, const Arabica::DOM::Element<std::string>& invokeElem, const std::string& invokeid);
	virtual void beforeTakingTransition(Interpreter interpreter, const Arabica::DOM::Element<std::string>& transition, bool moreComing);
	virtual void afterTakingTransition(Interpreter interpreter, const Arabica::DOM::Element<std::string>& transition, bool moreComing);
	virtual void beforeEnteringState(Interpreter interpreter, const Arabica::DOM::Element<std::string>& state, bool moreComing);
	virtual void afterEnteringState(Interpreter interpreter, const Arabica::DOM::Element<std::string>& state, bool moreComing);
	virtual void beforeInvoking(Interpreter interpreter, const Arabica::DOM::Element<std::string>& invokeElem, const std::string& invokeid);
	virtual void afterInvoking(Interpreter interpreter, const Arabica::DOM::Element<std::string>& invokeElem, const std::string& invokeid);
	virtual void afterMicroStep(Interpreter interpreter);
	virtual void onStableConfiguration(Interpreter interpreter);
	virtual void beforeCompletion(Interpreter interpreter) {}
	virtual void afterCompletion(Interpreter interpreter);

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
	void handleExecutable(Interpreter interpreter,
												const Arabica::DOM::Element<std::string>& execContentElem,
												Breakpoint::When when);
	void handleStable(Interpreter interpreter, Breakpoint::When when);
	void handleMicrostep(Interpreter interpreter, Breakpoint::When when);
	void handleEvent(Interpreter interpreter, const Event& event, Breakpoint::When when);

	tthread::recursive_mutex _sessionMutex;
  std::map<Interpreter, boost::shared_ptr<DebugSession> > _sessionForInterpreter;
};

}


#endif /* end of include guard: DEBUGGERMONITOR_H_Z050WPFH */
