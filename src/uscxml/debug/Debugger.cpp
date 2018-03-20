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
#include "uscxml/util/Predicates.h"
#include "uscxml/util/DOM.h"
#include "uscxml/debug/DebugSession.h"

namespace uscxml {

void Debugger::afterCompletion(const std::string& sessionId) {
	std::shared_ptr<DebugSession> session = getSession(sessionId);
	if (!session)
		return;

	Data msg;
	msg.compound["replyType"] = Data("finished", Data::VERBATIM);
	pushData(session, msg);
}

void Debugger::beforeCompletion(const std::string& sessionId) {}

std::list<Breakpoint> Debugger::getQualifiedStateBreakpoints(const std::string& sessionId, const XERCESC_NS::DOMElement* state, Breakpoint breakpointTemplate) {
	std::list<Breakpoint> breakpoints;

	Breakpoint bp = breakpointTemplate; // copy base as template
	bp.stateId = ATTR(state, kXMLCharId);
	bp.element = state;
	bp.subject = Breakpoint::STATE;
	breakpoints.push_back(bp);

	return breakpoints;
}

std::list<Breakpoint> Debugger::getQualifiedInvokeBreakpoints(const std::string& sessionId, const XERCESC_NS::DOMElement* invokeElem, const std::string invokeId, Breakpoint breakpointTemplate) {
	std::list<Breakpoint> breakpoints;

	Breakpoint bp = breakpointTemplate; // copy base as template
	bp.subject = Breakpoint::INVOKER;
	bp.element = invokeElem;
	bp.invokeId = invokeId;

	if (HAS_ATTR(invokeElem, kXMLCharType)) {
		bp.invokeType = ATTR(invokeElem, kXMLCharType);
	} else if (HAS_ATTR(invokeElem, kXMLCharTypeExpr)) {
		Interpreter intptr = Interpreter::fromSessionId(sessionId);
		bp.invokeType = intptr.getImpl()->evalAsData(ATTR(invokeElem, kXMLCharTypeExpr)).atom;
	}

	breakpoints.push_back(bp);

	return breakpoints;
}

std::list<Breakpoint> Debugger::getQualifiedTransBreakpoints(const std::string& sessionId, const XERCESC_NS::DOMElement* transition, Breakpoint breakpointTemplate) {
	std::list<Breakpoint> breakpoints;

	XERCESC_NS::DOMElement* source = getSourceState(transition);
	Interpreter intptr = Interpreter::fromSessionId(sessionId);

	std::list<XERCESC_NS::DOMElement*> targets = getTargetStates(transition, intptr.getImpl()->_scxml);

	for (auto target : targets) {

		Breakpoint bp = breakpointTemplate; // copy base as template
		bp.element = transition;
		bp.transSourceId = ATTR(source, kXMLCharId);
		bp.transTargetId = ATTR(target, kXMLCharId);
		bp.subject = Breakpoint::TRANSITION;

		breakpoints.push_back(bp);
	}

	return breakpoints;
}

void Debugger::beforeTakingTransition(const std::string& sessionId, const std::string& targetList, const XERCESC_NS::DOMElement* transition) {
	handleTransition(sessionId, transition, Breakpoint::BEFORE);
}
void Debugger::afterTakingTransition(const std::string& sessionId, const std::string& targetList, const XERCESC_NS::DOMElement* transition) {
	handleTransition(sessionId, transition, Breakpoint::AFTER);
}
void Debugger::beforeExecutingContent(const std::string& sessionId, const XERCESC_NS::DOMElement* execContent) {
	handleExecutable(sessionId, execContent, Breakpoint::BEFORE);
}
void Debugger::afterExecutingContent(const std::string& sessionId, const XERCESC_NS::DOMElement* execContent) {
	handleExecutable(sessionId, execContent, Breakpoint::AFTER);
}
void Debugger::beforeExitingState(const std::string& sessionId, const std::string& stateName, const XERCESC_NS::DOMElement* state) {
	handleState(sessionId, state, Breakpoint::BEFORE, Breakpoint::EXIT);
}
void Debugger::afterExitingState(const std::string& sessionId, const std::string& stateName, const XERCESC_NS::DOMElement* state) {
	handleState(sessionId, state, Breakpoint::AFTER, Breakpoint::EXIT);
}
void Debugger::beforeEnteringState(const std::string& sessionId, const std::string& stateName, const XERCESC_NS::DOMElement* state) {
	handleState(sessionId, state, Breakpoint::BEFORE, Breakpoint::ENTER);
}
void Debugger::afterEnteringState(const std::string& sessionId, const std::string& stateName, const XERCESC_NS::DOMElement* state) {
	handleState(sessionId, state, Breakpoint::AFTER, Breakpoint::ENTER);
}
void Debugger::beforeUninvoking(const std::string& sessionId, const XERCESC_NS::DOMElement* invokeElem, const std::string& invokeid) {
	handleInvoke(sessionId, invokeElem, invokeid, Breakpoint::BEFORE, Breakpoint::UNINVOKE);
}
void Debugger::afterUninvoking(const std::string& sessionId, const XERCESC_NS::DOMElement* invokeElem, const std::string& invokeid) {
	handleInvoke(sessionId, invokeElem, invokeid, Breakpoint::AFTER, Breakpoint::UNINVOKE);
}
void Debugger::beforeInvoking(const std::string& sessionId, const XERCESC_NS::DOMElement* invokeElem, const std::string& invokeid) {
	handleInvoke(sessionId, invokeElem, invokeid, Breakpoint::BEFORE, Breakpoint::INVOKE);
}
void Debugger::afterInvoking(const std::string& sessionId, const XERCESC_NS::DOMElement* invokeElem, const std::string& invokeid) {
	handleInvoke(sessionId, invokeElem, invokeid, Breakpoint::AFTER, Breakpoint::INVOKE);
}
void Debugger::onStableConfiguration(const std::string& sessionId) {
	handleStable(sessionId, Breakpoint::ON);
}
void Debugger::beforeMicroStep(const std::string& sessionId) {
	handleMicrostep(sessionId, Breakpoint::BEFORE);
}
void Debugger::afterMicroStep(const std::string& sessionId) {
	handleMicrostep(sessionId, Breakpoint::AFTER);
}
void Debugger::beforeProcessingEvent(const std::string& sessionId, const Event& event) {
	handleEvent(sessionId, event, Breakpoint::BEFORE);
}

void Debugger::handleExecutable(const std::string& sessionId,
                                const XERCESC_NS::DOMElement* execContentElem,
                                Breakpoint::When when) {
	std::shared_ptr<DebugSession> session = getSession(sessionId);
	if (!session)
		return;
	if (!session->_isRunning && !session->_isAttached)
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

void Debugger::handleEvent(const std::string& sessionId, const Event& event, Breakpoint::When when) {
	std::shared_ptr<DebugSession> session = getSession(sessionId);
	if (!session)
		return;
	if (!session->_isRunning && !session->_isAttached)
		return;

	std::list<Breakpoint> breakpoints;

	Breakpoint breakpoint;
	breakpoint.when = when;
	breakpoint.eventName = event.name;
	breakpoint.subject = Breakpoint::EVENT;
	breakpoints.push_back(breakpoint);

	session->checkBreakpoints(breakpoints);

}

void Debugger::handleStable(const std::string& sessionId, Breakpoint::When when) {
	std::shared_ptr<DebugSession> session = getSession(sessionId);
	if (!session)
		return;
	if (!session->_isRunning && !session->_isAttached)
		return;

	std::list<Breakpoint> breakpoints;

	Breakpoint breakpoint;
	breakpoint.when = when;
	breakpoint.subject = Breakpoint::STABLE;
	breakpoints.push_back(breakpoint);

	session->checkBreakpoints(breakpoints);
}

void Debugger::handleMicrostep(const std::string& sessionId, Breakpoint::When when) {
	std::shared_ptr<DebugSession> session = getSession(sessionId);
	if (!session)
		return;
	if (!session->_isRunning && !session->_isAttached)
		return;

	std::list<Breakpoint> breakpoints;

	Breakpoint breakpoint;
	breakpoint.when = when;
	breakpoint.subject = Breakpoint::MICROSTEP;
	breakpoints.push_back(breakpoint);

	session->checkBreakpoints(breakpoints);
}

void Debugger::handleTransition(const std::string& sessionId, const XERCESC_NS::DOMElement* transition, Breakpoint::When when) {
	std::shared_ptr<DebugSession> session = getSession(sessionId);
	if (!session)
		return;
	if (!session->_isRunning && !session->_isAttached)
		return;

	Breakpoint breakpointTemplate;
	breakpointTemplate.when = when;
	std::list<Breakpoint> qualifiedBreakpoints = getQualifiedTransBreakpoints(sessionId, transition, breakpointTemplate);
	session->checkBreakpoints(qualifiedBreakpoints);
}

void Debugger::handleState(const std::string& sessionId, const XERCESC_NS::DOMElement* state, Breakpoint::When when, Breakpoint::Action action) {
	std::shared_ptr<DebugSession> session = getSession(sessionId);
	if (!session)
		return;
	if (!session->_isRunning && !session->_isAttached)
		return;

	Breakpoint breakpointTemplate;
	breakpointTemplate.when = when;
	breakpointTemplate.action = action;
	std::list<Breakpoint> qualifiedBreakpoints = getQualifiedStateBreakpoints(sessionId, state, breakpointTemplate);
	session->checkBreakpoints(qualifiedBreakpoints);

}

void Debugger::handleInvoke(const std::string& sessionId, const XERCESC_NS::DOMElement* invokeElem, const std::string& invokeId, Breakpoint::When when, Breakpoint::Action action) {
	std::shared_ptr<DebugSession> session = getSession(sessionId);
	if (!session)
		return;
	if (!session->_isRunning && !session->_isAttached)
		return;

	Breakpoint breakpointTemplate;
	breakpointTemplate.when = when;
	breakpointTemplate.action = action;
	std::list<Breakpoint> qualifiedBreakpoints = getQualifiedInvokeBreakpoints(sessionId, invokeElem, invokeId, breakpointTemplate);
	session->checkBreakpoints(qualifiedBreakpoints);

}


}
