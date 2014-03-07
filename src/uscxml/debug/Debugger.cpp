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
	Data msg;
	msg.compound["replyType"] = Data("finished", Data::VERBATIM);
	pushData(msg);
}

std::list<Breakpoint> getQualifiedStateBreakpoints(Interpreter interpreter, const Arabica::DOM::Element<std::string>& state, Breakpoint breakpointTemplate) {
	std::list<Breakpoint> breakpoints;
		
	Breakpoint bp = breakpointTemplate; // copy base as template
	bp.stateId = ATTR(state, "id");
	bp.subject = Breakpoint::STATE;
	breakpoints.push_back(bp);
	
	return breakpoints;
}

std::list<Breakpoint> getQualifiedInvokeBreakpoints(Interpreter interpreter, const Arabica::DOM::Element<std::string>& invokeElem, const std::string invokeId, Breakpoint breakpointTemplate) {
	std::list<Breakpoint> breakpoints;
	
	Breakpoint bp = breakpointTemplate; // copy base as template
	bp.subject = Breakpoint::INVOKER;
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

void Debugger::handleEvent(Interpreter interpreter, const Event& event, Breakpoint::When when) {
	if (!interpreter.isRunning())
		return;
	
	std::list<Breakpoint> breakpoints;
	
	Breakpoint breakpoint;
	breakpoint.when = when;
	breakpoint.eventName = event.name;
	breakpoint.subject = Breakpoint::EVENT;
	breakpoints.push_back(breakpoint);
	
	checkBreakpoints(interpreter, breakpoints);

}
	
void Debugger::handleStable(Interpreter interpreter, Breakpoint::When when) {
	if (!interpreter.isRunning())
		return;

	std::list<Breakpoint> breakpoints;

	Breakpoint breakpoint;
	breakpoint.when = when;
	breakpoint.subject = Breakpoint::STABLE;
	breakpoints.push_back(breakpoint);
	
	checkBreakpoints(interpreter, breakpoints);
}

void Debugger::handleMicrostep(Interpreter interpreter, Breakpoint::When when) {
	if (!interpreter.isRunning())
		return;
	
	std::list<Breakpoint> breakpoints;
	
	Breakpoint breakpoint;
	breakpoint.when = when;
	breakpoint.subject = Breakpoint::MICROSTEP;
	breakpoints.push_back(breakpoint);
	
	checkBreakpoints(interpreter, breakpoints);
}

void Debugger::handleTransition(Interpreter interpreter, const Arabica::DOM::Element<std::string>& transition, Breakpoint::When when) {
	if (!interpreter.isRunning())
		return;

	Breakpoint breakpointTemplate;
	breakpointTemplate.when = when;
	std::list<Breakpoint> qualifiedBreakpoints = getQualifiedTransBreakpoints(interpreter, transition, breakpointTemplate);
	checkBreakpoints(interpreter, qualifiedBreakpoints);
}

void Debugger::handleState(Interpreter interpreter, const Arabica::DOM::Element<std::string>& state, Breakpoint::When when, Breakpoint::Action action) {
	if (!interpreter.isRunning())
		return;

	Breakpoint breakpointTemplate;
	breakpointTemplate.when = when;
	breakpointTemplate.action = action;
	std::list<Breakpoint> qualifiedBreakpoints = getQualifiedStateBreakpoints(interpreter, state, breakpointTemplate);
	checkBreakpoints(interpreter, qualifiedBreakpoints);

}

void Debugger::handleInvoke(Interpreter interpreter, const Arabica::DOM::Element<std::string>& invokeElem, const std::string& invokeId, Breakpoint::When when, Breakpoint::Action action) {
	if (!interpreter.isRunning())
		return;

	Breakpoint breakpointTemplate;
	breakpointTemplate.when = when;
	breakpointTemplate.action = action;
	std::list<Breakpoint> qualifiedBreakpoints = getQualifiedInvokeBreakpoints(interpreter, invokeElem, invokeId, breakpointTemplate);
	checkBreakpoints(interpreter, qualifiedBreakpoints);

}

void Debugger::checkBreakpoints(Interpreter interpreter, const std::list<Breakpoint> qualifiedBreakpoints) {
	std::list<Breakpoint>::const_iterator qualifiedBreakpointIter = qualifiedBreakpoints.begin();
	while(qualifiedBreakpointIter != qualifiedBreakpoints.end()) {
		const Breakpoint& qualifiedBreakpoint = *qualifiedBreakpointIter++;
		
		// check if one of the user-supplied breakpoints match
		bool userBreakpointMatched = false;
		std::set<Breakpoint>::const_iterator breakpointIter = _breakPoints.begin();
		while(breakpointIter != _breakPoints.end()) {
			const Breakpoint& breakpoint = *breakpointIter++;
			if (breakpoint.matches(qualifiedBreakpoint)) {
				Data replyData;
				replyData.compound["breakpoint"] = breakpoint.toData();
				replyData.compound["qualified"] = qualifiedBreakpoint.toData();
				
				userBreakpointMatched = true;
				hitBreakpoint(interpreter, replyData);
			}
		}
		if (_isStepping && !userBreakpointMatched) {
			Data replyData;
			replyData.compound["qualified"] = qualifiedBreakpoint.toData();
			hitBreakpoint(interpreter, replyData);
		}
	}
}

void Debugger::send(google::LogSeverity severity, const char* full_filename,
                  const char* base_filename, int line,
                  const struct ::tm* tm_time,
                  const char* message, size_t message_len) {
	
	// _sendQueue is thread-safe, not sure about ToString though

	LogMessage msg(severity,
								 full_filename,
								 base_filename,
								 line,
								 tm_time,
								 std::string(message, message_len),
								 ToString(severity, base_filename, line, tm_time, message, message_len));
	msg.compound["replyType"] = Data("log", Data::VERBATIM);
	pushData(msg);
}


}