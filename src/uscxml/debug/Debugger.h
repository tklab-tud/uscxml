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

	virtual void attachSession(InterpreterImpl* impl, std::shared_ptr<DebugSession> session) {
		std::lock_guard<std::recursive_mutex> lock(_sessionMutex);
		_sessionForInterpreter[impl] = session;
	}

	virtual void detachSession(InterpreterImpl* impl) {
		std::lock_guard<std::recursive_mutex> lock(_sessionMutex);
		_sessionForInterpreter.erase(impl);
	}

	virtual std::shared_ptr<DebugSession> getSession(InterpreterImpl* impl) {
		std::lock_guard<std::recursive_mutex> lock(_sessionMutex);
		if (_sessionForInterpreter.find(impl) != _sessionForInterpreter.end())
			return _sessionForInterpreter[impl];
		return std::shared_ptr<DebugSession>();
	}

	virtual void pushData(std::shared_ptr<DebugSession> session, Data pushData) = 0;

	// InterpreterMonitor
    virtual void beforeProcessingEvent(InterpreterImpl* impl, const Event& event);
    virtual void beforeMicroStep(InterpreterImpl* impl);
    virtual void beforeExitingState(InterpreterImpl* impl, const XERCESC_NS::DOMElement* state);
    virtual void afterExitingState(InterpreterImpl* impl, const XERCESC_NS::DOMElement* state);
    virtual void beforeExecutingContent(InterpreterImpl* impl, const XERCESC_NS::DOMElement* execContent);
    virtual void afterExecutingContent(InterpreterImpl* impl, const XERCESC_NS::DOMElement* execContent);
    virtual void beforeUninvoking(InterpreterImpl* impl, const XERCESC_NS::DOMElement* invokeElem, const std::string& invokeid);
    virtual void afterUninvoking(InterpreterImpl* impl, const XERCESC_NS::DOMElement* invokeElem, const std::string& invokeid);
    virtual void beforeTakingTransition(InterpreterImpl* impl, const XERCESC_NS::DOMElement* transition);
    virtual void afterTakingTransition(InterpreterImpl* impl, const XERCESC_NS::DOMElement* transition);
    virtual void beforeEnteringState(InterpreterImpl* impl, const XERCESC_NS::DOMElement* state);
    virtual void afterEnteringState(InterpreterImpl* impl, const XERCESC_NS::DOMElement* state);
    virtual void beforeInvoking(InterpreterImpl* impl, const XERCESC_NS::DOMElement* invokeElem, const std::string& invokeid);
    virtual void afterInvoking(InterpreterImpl* impl, const XERCESC_NS::DOMElement* invokeElem, const std::string& invokeid);
    virtual void afterMicroStep(InterpreterImpl* impl);
    virtual void onStableConfiguration(InterpreterImpl* impl);
    virtual void beforeCompletion(InterpreterImpl* impl);
    virtual void afterCompletion(InterpreterImpl* impl);

protected:

	void handleTransition(InterpreterImpl* impl,
	                      const XERCESC_NS::DOMElement* transition,
	                      Breakpoint::When when);
	void handleState(InterpreterImpl* impl,
	                 const XERCESC_NS::DOMElement* state,
	                 Breakpoint::When when,
	                 Breakpoint::Action action);
	void handleInvoke(InterpreterImpl* impl,
	                  const XERCESC_NS::DOMElement* invokeElem,
	                  const std::string& invokeId,
	                  Breakpoint::When when,
	                  Breakpoint::Action action);
	void handleExecutable(InterpreterImpl* impl,
	                      const XERCESC_NS::DOMElement* execContentElem,
	                      Breakpoint::When when);
	void handleStable(InterpreterImpl* impl, Breakpoint::When when);
	void handleMicrostep(InterpreterImpl* impl, Breakpoint::When when);
	void handleEvent(InterpreterImpl* impl, const Event& event, Breakpoint::When when);

    std::list<Breakpoint> getQualifiedTransBreakpoints(InterpreterImpl* impl,
                                                       const XERCESC_NS::DOMElement* transition,
                                                       Breakpoint breakpointTemplate);
    std::list<Breakpoint> getQualifiedStateBreakpoints(InterpreterImpl* impl,
                                                       const XERCESC_NS::DOMElement* state,
                                                       Breakpoint breakpointTemplate);
    std::list<Breakpoint> getQualifiedInvokeBreakpoints(InterpreterImpl* impl,
                                                        const XERCESC_NS::DOMElement* invokeElem,
                                                        const std::string invokeId,
                                                        Breakpoint breakpointTemplate);

	std::recursive_mutex _sessionMutex;
	std::map<InterpreterImpl*, std::shared_ptr<DebugSession> > _sessionForInterpreter;
};

}


#endif /* end of include guard: DEBUGGERMONITOR_H_Z050WPFH */
