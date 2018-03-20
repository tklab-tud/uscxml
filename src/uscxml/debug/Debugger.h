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

#include "uscxml/messages/Data.h"       // for Data
#include "uscxml/messages/Event.h"      // for Event
#include "uscxml/interpreter/InterpreterImpl.h"
#include "uscxml/debug/Breakpoint.h"

namespace uscxml {

class DebugSession;

class USCXML_API Debugger : public InterpreterMonitor {
public:
	Debugger() {
	}
	virtual ~Debugger() {}

	virtual void attachSession(const std::string& sessionId, std::shared_ptr<DebugSession> session) {
		std::lock_guard<std::recursive_mutex> lock(_sessionMutex);
		_sessionForInterpreter[sessionId] = session;
	}

	virtual void detachSession(const std::string& sessionId) {
		std::lock_guard<std::recursive_mutex> lock(_sessionMutex);
		_sessionForInterpreter.erase(sessionId);
	}

	virtual std::shared_ptr<DebugSession> getSession(const std::string& sessionId) {
		std::lock_guard<std::recursive_mutex> lock(_sessionMutex);
		if (_sessionForInterpreter.find(sessionId) != _sessionForInterpreter.end())
			return _sessionForInterpreter[sessionId];
		return std::shared_ptr<DebugSession>();
	}

	virtual void pushData(std::shared_ptr<DebugSession> session, Data pushData) = 0;

	// InterpreterMonitor
	virtual void beforeProcessingEvent(const std::string& sessionId, const Event& event);
	virtual void beforeMicroStep(const std::string& sessionId);
	virtual void beforeExitingState(const std::string& sessionId, const std::string& stateName, const XERCESC_NS::DOMElement* state);
	virtual void afterExitingState(const std::string& sessionId, const std::string& stateName, const XERCESC_NS::DOMElement* state);
	virtual void beforeExecutingContent(const std::string& sessionId, const XERCESC_NS::DOMElement* execContent);
	virtual void afterExecutingContent(const std::string& sessionId, const XERCESC_NS::DOMElement* execContent);
	virtual void beforeUninvoking(const std::string& sessionId, const XERCESC_NS::DOMElement* invokeElem, const std::string& invokeid);
	virtual void afterUninvoking(const std::string& sessionId, const XERCESC_NS::DOMElement* invokeElem, const std::string& invokeid);
	virtual void beforeTakingTransition(const std::string& sessionId, const std::string& targetList, const XERCESC_NS::DOMElement* transition);
	virtual void afterTakingTransition(const std::string& sessionId, const std::string& targetList, const XERCESC_NS::DOMElement* transition);
	virtual void beforeEnteringState(const std::string& sessionId, const std::string& stateName, const XERCESC_NS::DOMElement* state);
	virtual void afterEnteringState(const std::string& sessionId, const std::string& stateName, const XERCESC_NS::DOMElement* state);
	virtual void beforeInvoking(const std::string& sessionId, const XERCESC_NS::DOMElement* invokeElem, const std::string& invokeid);
	virtual void afterInvoking(const std::string& sessionId, const XERCESC_NS::DOMElement* invokeElem, const std::string& invokeid);
	virtual void afterMicroStep(const std::string& sessionId);
	virtual void onStableConfiguration(const std::string& sessionId);
	virtual void beforeCompletion(const std::string& sessionId);
	virtual void afterCompletion(const std::string& sessionId);

protected:

	void handleTransition(const std::string& sessionId,
	                      const XERCESC_NS::DOMElement* transition,
	                      Breakpoint::When when);
	void handleState(const std::string& sessionId,
	                 const XERCESC_NS::DOMElement* state,
	                 Breakpoint::When when,
	                 Breakpoint::Action action);
	void handleInvoke(const std::string& sessionId,
	                  const XERCESC_NS::DOMElement* invokeElem,
	                  const std::string& invokeId,
	                  Breakpoint::When when,
	                  Breakpoint::Action action);
	void handleExecutable(const std::string& sessionId,
	                      const XERCESC_NS::DOMElement* execContentElem,
	                      Breakpoint::When when);
	void handleStable(const std::string& sessionId, Breakpoint::When when);
	void handleMicrostep(const std::string& sessionId, Breakpoint::When when);
	void handleEvent(const std::string& sessionId, const Event& event, Breakpoint::When when);

	std::list<Breakpoint> getQualifiedTransBreakpoints(const std::string& sessionId,
	        const XERCESC_NS::DOMElement* transition,
	        Breakpoint breakpointTemplate);
	std::list<Breakpoint> getQualifiedStateBreakpoints(const std::string& sessionId,
	        const XERCESC_NS::DOMElement* state,
	        Breakpoint breakpointTemplate);
	std::list<Breakpoint> getQualifiedInvokeBreakpoints(const std::string& sessionId,
	        const XERCESC_NS::DOMElement* invokeElem,
	        const std::string invokeId,
	        Breakpoint breakpointTemplate);

	std::recursive_mutex _sessionMutex;
	/// @todo: We ought to change form InterpreterImpl to Interpreter everywhere
	std::map<std::string, std::shared_ptr<DebugSession> > _sessionForInterpreter;
};

}


#endif /* end of include guard: DEBUGGERMONITOR_H_Z050WPFH */
