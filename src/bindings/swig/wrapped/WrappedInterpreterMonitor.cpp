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

#include "WrappedInterpreterMonitor.h"
#include "uscxml/util/Predicates.h"
#include "uscxml/util/DOM.h"
#include <xercesc/dom/DOM.hpp>
#include <ostream>

namespace uscxml {

using namespace XERCESC_NS;

WrappedInterpreterMonitor::WrappedInterpreterMonitor() {}
WrappedInterpreterMonitor::~WrappedInterpreterMonitor() {}

void WrappedInterpreterMonitor::beforeExitingState(Interpreter& interpreter, const XERCESC_NS::DOMElement* state) {
	std::stringstream ss;
	ss << *state;
	beforeExitingState(ATTR(state, "id"), DOMUtils::xPathForNode(state), ss.str());
}

void WrappedInterpreterMonitor::afterExitingState(Interpreter& interpreter, const XERCESC_NS::DOMElement* state) {
	std::stringstream ss;
	ss << *state;
	afterExitingState(ATTR(state, "id"), DOMUtils::xPathForNode(state), ss.str());
}

void WrappedInterpreterMonitor::beforeExecutingContent(Interpreter& interpreter, const XERCESC_NS::DOMElement* content) {
	std::stringstream ss;
	ss << *content;
	beforeExecutingContent(TAGNAME(content), DOMUtils::xPathForNode(content), ss.str());
}

void WrappedInterpreterMonitor::afterExecutingContent(Interpreter& interpreter, const XERCESC_NS::DOMElement* content) {
	std::stringstream ss;
	ss << *content;
	afterExecutingContent(TAGNAME(content), DOMUtils::xPathForNode(content), ss.str());
}

void WrappedInterpreterMonitor::beforeUninvoking(Interpreter& interpreter, const XERCESC_NS::DOMElement* invoker, const std::string& invokeid) {
	std::stringstream ss;
	ss << *invoker;
	std::string invokeId;
	if (invoker->getUserData(X("invokeid")) != NULL) {
		invokeId = (char*)invoker->getUserData(X("invokeid"));
	}

	beforeUninvoking(DOMUtils::xPathForNode(invoker), invokeId, ss.str());
}

void WrappedInterpreterMonitor::afterUninvoking(Interpreter& interpreter, const XERCESC_NS::DOMElement* invoker, const std::string& invokeid) {
	std::stringstream ss;
	ss << *invoker;
	std::string invokeId;
	if (invoker->getUserData(X("invokeid")) != NULL) {
		invokeId = (char*)invoker->getUserData(X("invokeid"));
	}

	afterUninvoking(DOMUtils::xPathForNode(invoker), invokeId, ss.str());
}

void WrappedInterpreterMonitor::beforeTakingTransition(Interpreter& interpreter, const XERCESC_NS::DOMElement* transition) {
	XERCESC_NS::DOMElement* sourceState = getSourceState(transition);
	const XERCESC_NS::DOMElement* root = DOMUtils::getNearestAncestor(transition, "scxml");

	std::list<XERCESC_NS::DOMElement*> targetStates = getTargetStates(transition, root);

	std::stringstream ss;
	ss << *transition;

	std::list<std::string> targets;
	for (auto t : targetStates) {
		targets.push_back(ATTR_CAST(t, "id"));
	}

	beforeTakingTransition(DOMUtils::xPathForNode(transition), ATTR_CAST(sourceState, "id"), targets, ss.str());
}

void WrappedInterpreterMonitor::afterTakingTransition(Interpreter& interpreter, const XERCESC_NS::DOMElement* transition) {
	XERCESC_NS::DOMElement* sourceState = getSourceState(transition);
	const XERCESC_NS::DOMElement* root = DOMUtils::getNearestAncestor(transition, "scxml");

	std::list<XERCESC_NS::DOMElement*> targetStates = getTargetStates(transition, root);

	std::stringstream ss;
	ss << *transition;

	std::list<std::string> targets;
	for (auto t : targetStates) {
		targets.push_back(ATTR_CAST(t, "id"));
	}

	afterTakingTransition(DOMUtils::xPathForNode(transition), ATTR_CAST(sourceState, "id"), targets, ss.str());
}

void WrappedInterpreterMonitor::beforeEnteringState(Interpreter& interpreter, const XERCESC_NS::DOMElement* state) {
	std::stringstream ss;
	ss << *state;
	beforeEnteringState(ATTR(state, "id"), DOMUtils::xPathForNode(state), ss.str());
}

void WrappedInterpreterMonitor::afterEnteringState(Interpreter& interpreter, const XERCESC_NS::DOMElement* state) {
	std::stringstream ss;
	ss << *state;
	afterEnteringState(ATTR(state, "id"), DOMUtils::xPathForNode(state), ss.str());
}

void WrappedInterpreterMonitor::beforeInvoking(Interpreter& interpreter, const XERCESC_NS::DOMElement* invoker, const std::string& invokeid) {
	std::stringstream ss;
	ss << *invoker;
	std::string invokeId;
	if (invoker->getUserData(X("invokeid")) != NULL) {
		invokeId = (char*)invoker->getUserData(X("invokeid"));
	}

	beforeInvoking(DOMUtils::xPathForNode(invoker), invokeId, ss.str());
}

void WrappedInterpreterMonitor::afterInvoking(Interpreter& interpreter, const XERCESC_NS::DOMElement* invoker, const std::string& invokeid) {
	std::stringstream ss;
	ss << *invoker;
	std::string invokeId;
	if (invoker->getUserData(X("invokeid")) != NULL) {
		invokeId = (char*)invoker->getUserData(X("invokeid"));
	}

	afterInvoking(DOMUtils::xPathForNode(invoker), invokeId, ss.str());
}

}