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

#include "uscxml/debug/Debugger.h"
#include "uscxml/util/DOM.h"
#include "uscxml/util/Predicates.h"
#include "uscxml/debug/DebugSession.h"

namespace uscxml {

void Debugger::afterCompletion(InterpreterImpl* impl) {
	std::shared_ptr<DebugSession> session = getSession(impl);
	if (!session)
		return;

	Data msg;
	msg.compound["replyType"] = Data("finished", Data::VERBATIM);
	pushData(session, msg);
}

void Debugger::beforeCompletion(InterpreterImpl* impl) {}

std::list<Breakpoint> Debugger::getQualifiedStateBreakpoints(InterpreterImpl* impl, const XERCESC_NS::DOMElement* state, Breakpoint breakpointTemplate) {
	std::list<Breakpoint> breakpoints;

	Breakpoint bp = breakpointTemplate; // copy base as template
	bp.stateId = ATTR(state, "id");
	bp.element = state;
	bp.subject = Breakpoint::STATE;
	breakpoints.push_back(bp);

	return breakpoints;
}

std::list<Breakpoint> Debugger::getQualifiedInvokeBreakpoints(InterpreterImpl* impl, const XERCESC_NS::DOMElement* invokeElem, const std::string invokeId, Breakpoint breakpointTemplate) {
	std::list<Breakpoint> breakpoints;

	Breakpoint bp = breakpointTemplate; // copy base as template
	bp.subject = Breakpoint::INVOKER;
	bp.element = invokeElem;
	bp.invokeId = invokeId;

	if (HAS_ATTR(invokeElem, "type")) {
		bp.invokeType = ATTR(invokeElem, "type");
	} else if (HAS_ATTR(invokeElem, "typeexpr")) {
		bp.invokeType = impl->evalAsData(ATTR(invokeElem, "typeexpr")).atom;
	}

	breakpoints.push_back(bp);

	return breakpoints;
}

std::list<Breakpoint> Debugger::getQualifiedTransBreakpoints(InterpreterImpl* impl, const XERCESC_NS::DOMElement* transition, Breakpoint breakpointTemplate) {
	std::list<Breakpoint> breakpoints;

	XERCESC_NS::DOMElement* source = getSourceState(transition);
    std::list<XERCESC_NS::DOMElement*> targets = getTargetStates(transition, impl->_scxml);

    for (auto target : targets) {

		Breakpoint bp = breakpointTemplate; // copy base as template
		bp.element = transition;
		bp.transSourceId = ATTR(source, "id");
		bp.transTargetId = ATTR(target, "id");
		bp.subject = Breakpoint::TRANSITION;

		breakpoints.push_back(bp);
	}

	return breakpoints;
}

void Debugger::beforeTakingTransition(InterpreterImpl* impl, const XERCESC_NS::DOMElement* transition) {
	handleTransition(impl, transition, Breakpoint::BEFORE);
}
void Debugger::afterTakingTransition(InterpreterImpl* impl, const XERCESC_NS::DOMElement* transition) {
	handleTransition(impl, transition, Breakpoint::AFTER);
}
void Debugger::beforeExecutingContent(InterpreterImpl* impl, const XERCESC_NS::DOMElement* execContent) {
	handleExecutable(impl, execContent, Breakpoint::BEFORE);
}
void Debugger::afterExecutingContent(InterpreterImpl* impl, const XERCESC_NS::DOMElement* execContent) {
	handleExecutable(impl, execContent, Breakpoint::AFTER);
}
void Debugger::beforeExitingState(InterpreterImpl* impl, const XERCESC_NS::DOMElement* state) {
	handleState(impl, state, Breakpoint::BEFORE, Breakpoint::EXIT);
}
void Debugger::afterExitingState(InterpreterImpl* impl, const XERCESC_NS::DOMElement* state) {
	handleState(impl, state, Breakpoint::AFTER, Breakpoint::EXIT);
}
void Debugger::beforeEnteringState(InterpreterImpl* impl, const XERCESC_NS::DOMElement* state) {
	handleState(impl, state, Breakpoint::BEFORE, Breakpoint::ENTER);
}
void Debugger::afterEnteringState(InterpreterImpl* impl, const XERCESC_NS::DOMElement* state) {
	handleState(impl, state, Breakpoint::AFTER, Breakpoint::ENTER);
}
void Debugger::beforeUninvoking(InterpreterImpl* impl, const XERCESC_NS::DOMElement* invokeElem, const std::string& invokeid) {
	handleInvoke(impl, invokeElem, invokeid, Breakpoint::BEFORE, Breakpoint::UNINVOKE);
}
void Debugger::afterUninvoking(InterpreterImpl* impl, const XERCESC_NS::DOMElement* invokeElem, const std::string& invokeid) {
	handleInvoke(impl, invokeElem, invokeid, Breakpoint::AFTER, Breakpoint::UNINVOKE);
}
void Debugger::beforeInvoking(InterpreterImpl* impl, const XERCESC_NS::DOMElement* invokeElem, const std::string& invokeid) {
	handleInvoke(impl, invokeElem, invokeid, Breakpoint::BEFORE, Breakpoint::INVOKE);
}
void Debugger::afterInvoking(InterpreterImpl* impl, const XERCESC_NS::DOMElement* invokeElem, const std::string& invokeid) {
	handleInvoke(impl, invokeElem, invokeid, Breakpoint::AFTER, Breakpoint::INVOKE);
}
void Debugger::onStableConfiguration(InterpreterImpl* impl) {
	handleStable(impl, Breakpoint::ON);
}
void Debugger::beforeMicroStep(InterpreterImpl* impl) {
	handleMicrostep(impl, Breakpoint::BEFORE);
}
void Debugger::afterMicroStep(InterpreterImpl* impl) {
	handleMicrostep(impl, Breakpoint::AFTER);
}
void Debugger::beforeProcessingEvent(InterpreterImpl* impl, const Event& event) {
	handleEvent(impl, event, Breakpoint::BEFORE);
}

void Debugger::handleExecutable(InterpreterImpl* impl,
                                const XERCESC_NS::DOMElement* execContentElem,
                                Breakpoint::When when) {
	std::shared_ptr<DebugSession> session = getSession(impl);
	if (!session)
		return;
    if (!session->_isRunning)
        return;
    
	std::list<Breakpoint> breakpoints;

	Breakpoint breakpoint;
	breakpoint.when = when;
	breakpoint.element = execContentElem;
	breakpoint.executableName = X(execContentElem->getLocalName()).str();
	breakpoint.subject = Breakpoint::EXECUTABLE;
	breakpoints.push_back(breakpoint);

	session->checkBreakpoints(breakpoints);

}

void Debugger::handleEvent(InterpreterImpl* impl, const Event& event, Breakpoint::When when) {
    std::shared_ptr<DebugSession> session = getSession(impl);
    if (!session)
        return;
    if (!session->_isRunning)
        return;

	std::list<Breakpoint> breakpoints;

	Breakpoint breakpoint;
	breakpoint.when = when;
	breakpoint.eventName = event.name;
	breakpoint.subject = Breakpoint::EVENT;
	breakpoints.push_back(breakpoint);

	session->checkBreakpoints(breakpoints);

}

void Debugger::handleStable(InterpreterImpl* impl, Breakpoint::When when) {
    std::shared_ptr<DebugSession> session = getSession(impl);
    if (!session)
        return;
    if (!session->_isRunning)
        return;

	std::list<Breakpoint> breakpoints;

	Breakpoint breakpoint;
	breakpoint.when = when;
	breakpoint.subject = Breakpoint::STABLE;
	breakpoints.push_back(breakpoint);

	session->checkBreakpoints(breakpoints);
}

void Debugger::handleMicrostep(InterpreterImpl* impl, Breakpoint::When when) {
    std::shared_ptr<DebugSession> session = getSession(impl);
    if (!session)
        return;
    if (!session->_isRunning)
        return;

	std::list<Breakpoint> breakpoints;

	Breakpoint breakpoint;
	breakpoint.when = when;
	breakpoint.subject = Breakpoint::MICROSTEP;
	breakpoints.push_back(breakpoint);

	session->checkBreakpoints(breakpoints);
}

void Debugger::handleTransition(InterpreterImpl* impl, const XERCESC_NS::DOMElement* transition, Breakpoint::When when) {
    std::shared_ptr<DebugSession> session = getSession(impl);
    if (!session)
        return;
    if (!session->_isRunning)
        return;

	Breakpoint breakpointTemplate;
	breakpointTemplate.when = when;
	std::list<Breakpoint> qualifiedBreakpoints = getQualifiedTransBreakpoints(impl, transition, breakpointTemplate);
	session->checkBreakpoints(qualifiedBreakpoints);
}

void Debugger::handleState(InterpreterImpl* impl, const XERCESC_NS::DOMElement* state, Breakpoint::When when, Breakpoint::Action action) {
    std::shared_ptr<DebugSession> session = getSession(impl);
    if (!session)
        return;
    if (!session->_isRunning)
        return;

	Breakpoint breakpointTemplate;
	breakpointTemplate.when = when;
	breakpointTemplate.action = action;
	std::list<Breakpoint> qualifiedBreakpoints = getQualifiedStateBreakpoints(impl, state, breakpointTemplate);
	session->checkBreakpoints(qualifiedBreakpoints);

}

void Debugger::handleInvoke(InterpreterImpl* impl, const XERCESC_NS::DOMElement* invokeElem, const std::string& invokeId, Breakpoint::When when, Breakpoint::Action action) {
    std::shared_ptr<DebugSession> session = getSession(impl);
    if (!session)
        return;
    if (!session->_isRunning)
        return;

	Breakpoint breakpointTemplate;
	breakpointTemplate.when = when;
	breakpointTemplate.action = action;
	std::list<Breakpoint> qualifiedBreakpoints = getQualifiedInvokeBreakpoints(impl, invokeElem, invokeId, breakpointTemplate);
	session->checkBreakpoints(qualifiedBreakpoints);

}


}