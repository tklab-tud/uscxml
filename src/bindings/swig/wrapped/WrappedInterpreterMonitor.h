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

#ifndef WRAPPEDINTERPRETERMONITOR_H_F5C83A0D
#define WRAPPEDINTERPRETERMONITOR_H_F5C83A0D

#include <vector>
#include <list>
#include <ostream>
#include <string>

#include <DOM/Document.hpp>
#include <DOM/io/Stream.hpp>

#include "../../../uscxml/Message.h"
#include "../../../uscxml/Factory.h"
#include "../../../uscxml/Interpreter.h"
#include "../../../uscxml/dom/DOMUtils.h"

namespace uscxml {

class WrappedInterpreterMonitor : public InterpreterMonitor {
public:
	WrappedInterpreterMonitor();
	virtual ~WrappedInterpreterMonitor();

	virtual void beforeExitingState(Interpreter interpreter,
	                                const Arabica::DOM::Element<std::string>& state,
	                                bool moreComing) {
		std::stringstream ss;
		ss << state;
		beforeExitingState(interpreter, state.getAttribute("id"), DOMUtils::xPathForNode(state), ss.str(), moreComing);
	}
	virtual void beforeExitingState(Interpreter interpreter,
	                                const std::string& stateId,
	                                const std::string& xpath,
	                                const std::string& state,
	                                bool moreComing) {}


	virtual void afterExitingState(Interpreter interpreter,
	                               const Arabica::DOM::Element<std::string>& state,
	                               bool moreComing) {
		std::stringstream ss;
		ss << state;
		afterExitingState(interpreter, state.getAttribute("id"), DOMUtils::xPathForNode(state), ss.str(), moreComing);
	}
	virtual void afterExitingState(Interpreter interpreter,
	                               const std::string& stateId,
	                               const std::string& xpath,
	                               const std::string& state,
	                               bool moreComing) {	}


	virtual void beforeExecutingContent(Interpreter interpreter,
	                                    const Arabica::DOM::Element<std::string>& element) {
		std::stringstream ss;
		ss << element;
		beforeExecutingContent(interpreter, element.getTagName(), DOMUtils::xPathForNode(element), ss.str());
	}
	virtual void beforeExecutingContent(Interpreter interpreter,
	                                    const std::string& tagName,
	                                    const std::string& xpath,
	                                    const std::string& element) {}


	virtual void afterExecutingContent(Interpreter interpreter,
	                                   const Arabica::DOM::Element<std::string>& element) {
		std::stringstream ss;
		ss << element;
		afterExecutingContent(interpreter, element.getTagName(), DOMUtils::xPathForNode(element), ss.str());
	}
	virtual void afterExecutingContent(Interpreter interpreter,
	                                   const std::string& tagName,
	                                   const std::string& xpath,
	                                   const std::string& element) {}


	virtual void beforeUninvoking(Interpreter interpreter,
	                              const Arabica::DOM::Element<std::string>& invokeElem,
	                              const std::string& invokeid) {
		std::stringstream ss;
		ss << invokeElem;
		beforeUninvoking(interpreter, DOMUtils::xPathForNode(invokeElem), invokeid, ss.str());
	}
	virtual void beforeUninvoking(Interpreter interpreter,
	                              const std::string& xpath,
	                              const std::string& invokeid,
	                              const std::string& element) {}


	virtual void afterUninvoking(Interpreter interpreter,
	                             const Arabica::DOM::Element<std::string>& invokeElem,
	                             const std::string& invokeid) {
		std::stringstream ss;
		ss << invokeElem;
		afterUninvoking(interpreter, DOMUtils::xPathForNode(invokeElem), invokeid, ss.str());
	}
	virtual void afterUninvoking(Interpreter interpreter,
	                             const std::string& xpath,
	                             const std::string& invokeid,
	                             const std::string& element) {}


	virtual void beforeTakingTransition(Interpreter interpreter,
	                                    const Arabica::DOM::Element<std::string>& transition,
	                                    bool moreComing) {
		Arabica::DOM::Node<std::string> sourceState = interpreter.getImpl()->getSourceState(transition);
		Arabica::XPath::NodeSet<std::string> targetStates = interpreter.getImpl()->getTargetStates(transition);

		std::stringstream ss;
		ss << transition;

		std::list<std::string> targets;
		for (int i = 0; i < targetStates.size(); i++) {
			targets.push_back(ATTR_CAST(targetStates[i], "id"));
		}

		beforeTakingTransition(interpreter, DOMUtils::xPathForNode(transition), ATTR_CAST(sourceState, "id"), targets, ss.str(), moreComing);
	}
	virtual void beforeTakingTransition(Interpreter interpreter,
	                                    const std::string& xpath,
	                                    const std::string& source,
	                                    const std::list<std::string>& targets,
	                                    const std::string& element,
	                                    bool moreComing) {}

	virtual void afterTakingTransition(Interpreter interpreter,
	                                   const Arabica::DOM::Element<std::string>& transition,
	                                   bool moreComing) {
		Arabica::DOM::Node<std::string> sourceState = interpreter.getImpl()->getSourceState(transition);
		Arabica::XPath::NodeSet<std::string> targetStates = interpreter.getImpl()->getTargetStates(transition);

		std::stringstream ss;
		ss << transition;

		std::list<std::string> targets;
		for (int i = 0; i < targetStates.size(); i++) {
			targets.push_back(ATTR_CAST(targetStates[i], "id"));
		}

		afterTakingTransition(interpreter, DOMUtils::xPathForNode(transition), ATTR_CAST(sourceState, "id"), targets, ss.str(), moreComing);
	}
	virtual void afterTakingTransition(Interpreter interpreter,
	                                   const std::string& xpath,
	                                   const std::string& source,
	                                   const std::list<std::string>& targets,
	                                   const std::string& element,
	                                   bool moreComing) {}


	virtual void beforeEnteringState(Interpreter interpreter,
	                                 const Arabica::DOM::Element<std::string>& state,
	                                 bool moreComing) {
		std::stringstream ss;
		ss << state;
		beforeEnteringState(interpreter, state.getAttribute("id"), DOMUtils::xPathForNode(state), ss.str(), moreComing);
	}
	virtual void beforeEnteringState(Interpreter interpreter,
	                                 const std::string& stateId,
	                                 const std::string& xpath,
	                                 const std::string& state,
	                                 bool moreComing) {}


	virtual void afterEnteringState(Interpreter interpreter,
	                                const Arabica::DOM::Element<std::string>& state,
	                                bool moreComing) {
		std::stringstream ss;
		ss << state;
		afterEnteringState(interpreter, state.getAttribute("id"), DOMUtils::xPathForNode(state), ss.str(), moreComing);
	}
	virtual void afterEnteringState(Interpreter interpreter,
	                                const std::string& stateId,
	                                const std::string& xpath,
	                                const std::string& state,
	                                bool moreComing) {}


	virtual void beforeInvoking(Interpreter interpreter,
	                            const Arabica::DOM::Element<std::string>& invokeElem,
	                            const std::string& invokeid) {
		std::stringstream ss;
		ss << invokeElem;
		beforeInvoking(interpreter, DOMUtils::xPathForNode(invokeElem), invokeid, ss.str());
	}
	virtual void beforeInvoking(Interpreter interpreter,
	                            const std::string& xpath,
	                            const std::string& invokeid,
	                            const std::string& element) {}

	virtual void afterInvoking(Interpreter interpreter,
	                           const Arabica::DOM::Element<std::string>& invokeElem,
	                           const std::string& invokeid) {
		std::stringstream ss;
		ss << invokeElem;
		afterInvoking(interpreter, DOMUtils::xPathForNode(invokeElem), invokeid, ss.str());
	}
	virtual void afterInvoking(Interpreter interpreter,
	                           const std::string& xpath,
	                           const std::string& invokeid,
	                           const std::string& element) {}

	virtual void reportIssue(Interpreter interpreter, const InterpreterIssue& issue) {}
};

}


#endif /* end of include guard: WRAPPEDINTERPRETERMONITOR_H_F5C83A0D */
