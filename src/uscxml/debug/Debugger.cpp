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
#include "uscxml/DOMUtils.h"

namespace uscxml {
	
void Debugger::afterCompletion(Interpreter interpreter) {
	boost::shared_ptr<DebugSession> session = getSession(interpreter);
	if (!session)
		return;

	Data msg;
	msg.compound["replyType"] = Data("finished", Data::VERBATIM);
	pushData(session, msg);
}

std::list<Breakpoint> getQualifiedStateBreakpoints(Interpreter interpreter, const Arabica::DOM::Element<std::string>& state, Breakpoint breakpointTemplate) {
	std::list<Breakpoint> breakpoints;
		
	Breakpoint bp = breakpointTemplate; // copy base as template
	bp.stateId = ATTR(state, "id");
	bp.element = state;
	bp.subject = Breakpoint::STATE;
	breakpoints.push_back(bp);
	
	return breakpoints;
}

std::list<Breakpoint> getQualifiedInvokeBreakpoints(Interpreter interpreter, const Arabica::DOM::Element<std::string>& invokeElem, const std::string invokeId, Breakpoint breakpointTemplate) {
	std::list<Breakpoint> breakpoints;
	
	Breakpoint bp = breakpointTemplate; // copy base as template
	bp.subject = Breakpoint::INVOKER;
	bp.element = invokeElem;
	bp.invokeId = invokeId;
		
	if (HAS_ATTR(invokeElem, "type")) {
		bp.invokeType = ATTR(invokeElem, "type");
	} else if (HAS_ATTR(invokeElem, "typeexpr")) {
		bp.invokeType = interpreter.getDataModel().evalAsString(ATTR(invokeElem, "typeexpr"));
	}
		
	breakpoints.push_back(bp);
	
	return breakpoints;
}

std::list<Breakpoint> getQualifiedTransBreakpoints(Interpreter interpreter, const Arabica::DOM::Element<std::string>& transition, Breakpoint breakpointTemplate) {
	std::list<Breakpoint> breakpoints;
	
	Arabica::DOM::Element<std::string> source(interpreter.getSourceState(transition));
	Arabica::XPath::NodeSet<std::string> targets = interpreter.getTargetStates(transition);

	for (int j = 0; j < targets.size(); j++) {
		Arabica::DOM::Element<std::string> target(targets[j]);
		
		Breakpoint bp = breakpointTemplate; // copy base as template
		bp.element = transition;
		bp.transSource = ATTR(source, "id");
		bp.transTarget = ATTR(target, "id");
		bp.subject = Breakpoint::TRANSITION;

		breakpoints.push_back(bp);
	}

	return breakpoints;
}

void Debugger::beforeTakingTransition(Interpreter interpreter, const Arabica::DOM::Element<std::string>& transition) {
	handleTransition(interpreter, transition, Breakpoint::BEFORE);
}
void Debugger::afterTakingTransition(Interpreter interpreter, const Arabica::DOM::Element<std::string>& transition) {
	handleTransition(interpreter, transition, Breakpoint::AFTER);
}
void Debugger::beforeExecutingContent(Interpreter interpreter, const Arabica::DOM::Node<std::string>& content) {
	handleExecutable(interpreter, Arabica::DOM::Element<std::string>(content), Breakpoint::BEFORE);
}
void Debugger::afterExecutingContent(Interpreter interpreter, const Arabica::DOM::Node<std::string>& content) {
	handleExecutable(interpreter, Arabica::DOM::Element<std::string>(content), Breakpoint::AFTER);
}
void Debugger::beforeExitingState(Interpreter interpreter, const Arabica::DOM::Element<std::string>& state) {
	handleState(interpreter, state, Breakpoint::BEFORE, Breakpoint::EXIT);
}
void Debugger::afterExitingState(Interpreter interpreter, const Arabica::DOM::Element<std::string>& state) {
	handleState(interpreter, state, Breakpoint::AFTER, Breakpoint::EXIT);
}
void Debugger::beforeEnteringState(Interpreter interpreter, const Arabica::DOM::Element<std::string>& state) {
	handleState(interpreter, state, Breakpoint::BEFORE, Breakpoint::ENTER);
}
void Debugger::afterEnteringState(Interpreter interpreter, const Arabica::DOM::Element<std::string>& state) {
	handleState(interpreter, state, Breakpoint::AFTER, Breakpoint::ENTER);
}
void Debugger::beforeUninvoking(Interpreter interpreter, const Arabica::DOM::Element<std::string>& invokeElem, const std::string& invokeid) {
	handleInvoke(interpreter, invokeElem, invokeid, Breakpoint::BEFORE, Breakpoint::UNINVOKE);
}
void Debugger::afterUninvoking(Interpreter interpreter, const Arabica::DOM::Element<std::string>& invokeElem, const std::string& invokeid) {
	handleInvoke(interpreter, invokeElem, invokeid, Breakpoint::AFTER, Breakpoint::UNINVOKE);
}
void Debugger::beforeInvoking(Interpreter interpreter, const Arabica::DOM::Element<std::string>& invokeElem, const std::string& invokeid) {
	handleInvoke(interpreter, invokeElem, invokeid, Breakpoint::BEFORE, Breakpoint::INVOKE);
}
void Debugger::afterInvoking(Interpreter interpreter, const Arabica::DOM::Element<std::string>& invokeElem, const std::string& invokeid) {
	handleInvoke(interpreter, invokeElem, invokeid, Breakpoint::AFTER, Breakpoint::INVOKE);
}
void Debugger::onStableConfiguration(Interpreter interpreter) {
	handleStable(interpreter, Breakpoint::ON);
}
void Debugger::beforeMicroStep(Interpreter interpreter) {
	handleMicrostep(interpreter, Breakpoint::BEFORE);
}
void Debugger::afterMicroStep(Interpreter interpreter) {
	handleMicrostep(interpreter, Breakpoint::AFTER);
}
void Debugger::beforeProcessingEvent(Interpreter interpreter, const Event& event) {
	handleEvent(interpreter, event, Breakpoint::BEFORE);
}

void Debugger::handleExecutable(Interpreter interpreter,
																const Arabica::DOM::Element<std::string>& execContentElem,
																Breakpoint::When when) {
	if (!interpreter.isRunning())
		return;
	boost::shared_ptr<DebugSession> session = getSession(interpreter);
	if (!session)
		return;
	
	std::list<Breakpoint> breakpoints;

	Breakpoint breakpoint;
	breakpoint.when = when;
	breakpoint.element = execContentElem;
	breakpoint.executableName = execContentElem.getLocalName();
	breakpoint.subject = Breakpoint::EXECUTABLE;
	breakpoints.push_back(breakpoint);
	
	session->checkBreakpoints(breakpoints);

}

void Debugger::handleEvent(Interpreter interpreter, const Event& event, Breakpoint::When when) {
	if (!interpreter.isRunning())
		return;
	boost::shared_ptr<DebugSession> session = getSession(interpreter);
	if (!session)
		return;
	
	std::list<Breakpoint> breakpoints;
	
	Breakpoint breakpoint;
	breakpoint.when = when;
	breakpoint.eventName = event.name;
	breakpoint.subject = Breakpoint::EVENT;
	breakpoints.push_back(breakpoint);
	
	session->checkBreakpoints(breakpoints);

}
	
void Debugger::handleStable(Interpreter interpreter, Breakpoint::When when) {
	if (!interpreter.isRunning())
		return;
	boost::shared_ptr<DebugSession> session = getSession(interpreter);
	if (!session)
		return;

	std::list<Breakpoint> breakpoints;

	Breakpoint breakpoint;
	breakpoint.when = when;
	breakpoint.subject = Breakpoint::STABLE;
	breakpoints.push_back(breakpoint);
	
	session->checkBreakpoints(breakpoints);
}

void Debugger::handleMicrostep(Interpreter interpreter, Breakpoint::When when) {
	if (!interpreter.isRunning())
		return;
	boost::shared_ptr<DebugSession> session = getSession(interpreter);
	if (!session)
		return;

	std::list<Breakpoint> breakpoints;
	
	Breakpoint breakpoint;
	breakpoint.when = when;
	breakpoint.subject = Breakpoint::MICROSTEP;
	breakpoints.push_back(breakpoint);
	
	session->checkBreakpoints(breakpoints);
}

void Debugger::handleTransition(Interpreter interpreter, const Arabica::DOM::Element<std::string>& transition, Breakpoint::When when) {
	if (!interpreter.isRunning())
		return;
	boost::shared_ptr<DebugSession> session = getSession(interpreter);
	if (!session)
		return;

	Breakpoint breakpointTemplate;
	breakpointTemplate.when = when;
	std::list<Breakpoint> qualifiedBreakpoints = getQualifiedTransBreakpoints(interpreter, transition, breakpointTemplate);
	session->checkBreakpoints(qualifiedBreakpoints);
}

void Debugger::handleState(Interpreter interpreter, const Arabica::DOM::Element<std::string>& state, Breakpoint::When when, Breakpoint::Action action) {
	if (!interpreter.isRunning())
		return;
	boost::shared_ptr<DebugSession> session = getSession(interpreter);
	if (!session)
		return;

	Breakpoint breakpointTemplate;
	breakpointTemplate.when = when;
	breakpointTemplate.action = action;
	std::list<Breakpoint> qualifiedBreakpoints = getQualifiedStateBreakpoints(interpreter, state, breakpointTemplate);
	session->checkBreakpoints(qualifiedBreakpoints);

}

void Debugger::handleInvoke(Interpreter interpreter, const Arabica::DOM::Element<std::string>& invokeElem, const std::string& invokeId, Breakpoint::When when, Breakpoint::Action action) {
	if (!interpreter.isRunning())
		return;
	boost::shared_ptr<DebugSession> session = getSession(interpreter);
	if (!session)
		return;

	Breakpoint breakpointTemplate;
	breakpointTemplate.when = when;
	breakpointTemplate.action = action;
	std::list<Breakpoint> qualifiedBreakpoints = getQualifiedInvokeBreakpoints(interpreter, invokeElem, invokeId, breakpointTemplate);
	session->checkBreakpoints(qualifiedBreakpoints);

}


}