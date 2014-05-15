/**
 *  @file
 *  @author     2012-2013 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#include "InterpreterDraft6.h"

#include <glog/logging.h>
#include "uscxml/UUID.h"
#include "uscxml/DOMUtils.h"

#define VERBOSE 0

namespace uscxml {

using namespace Arabica::XPath;
using namespace Arabica::DOM;

// see: http://www.w3.org/TR/scxml/#AlgorithmforSCXMLInterpretation
	
void InterpreterDraft6::interpret() {
	InterpreterState state;
	while(true) {
		state = step(true);
		
		switch (state) {
			case uscxml::INIT_FAILED:
			case uscxml::FINISHED:
			case uscxml::INTERRUPTED:
				// return as we finished
				return;
			case uscxml::NOTHING_TODO:
				// die as this can never happen with a blocking call
				assert(false);
			case uscxml::INITIALIZED:
			case uscxml::PROCESSED:
				
				// process invokers on main thread
				if(_thread == NULL) {
					runOnMainThread(200);
				}

				// process next step
				break;
		}
	}
}

// setup / fetch the documents initial transitions
NodeSet<std::string> InterpreterDraft6::getDocumentInitialTransitions() {
	NodeSet<std::string> initialTransitions;
	
	if (_userDefinedStartConfiguration.size() > 0) {
		// we emulate entering a given configuration by creating a pseudo deep history
		Element<std::string> initHistory = _document.createElementNS(_nsInfo.nsURL, "history");
		_nsInfo.setPrefix(initHistory);
		
		initHistory.setAttribute("id", UUID::getUUID());
		initHistory.setAttribute("type", "deep");
		_scxml.insertBefore(initHistory, _scxml.getFirstChild());
		
		std::string histId = ATTR(initHistory, "id");
		NodeSet<std::string> histStates;
		for (int i = 0; i < _userDefinedStartConfiguration.size(); i++) {
			histStates.push_back(getState(_userDefinedStartConfiguration[i]));
		}
		_historyValue[histId] = histStates;
		
		Element<std::string> initialElem = _document.createElementNS(_nsInfo.nsURL, "initial");
		_nsInfo.setPrefix(initialElem);
		
		initialElem.setAttribute("generated", "true");
		Element<std::string> transitionElem = _document.createElementNS(_nsInfo.nsURL, "transition");
		_nsInfo.setPrefix(transitionElem);
		
		transitionElem.setAttribute("target", histId);
		initialElem.appendChild(transitionElem);
		_scxml.appendChild(initialElem);
		initialTransitions.push_back(transitionElem);
		
	} else {
		// try to get initial transition from initial element
		initialTransitions = _xpath.evaluate("/" + _nsInfo.xpathPrefix + "initial/" + _nsInfo.xpathPrefix + "transition", _scxml).asNodeSet();
		if (initialTransitions.size() == 0) {
			Arabica::XPath::NodeSet<std::string> initialStates;
			// fetch per draft
			initialStates = getInitialStates();
			assert(initialStates.size() > 0);
			for (int i = 0; i < initialStates.size(); i++) {
				Element<std::string> initialElem = _document.createElementNS(_nsInfo.nsURL, "initial");
				_nsInfo.setPrefix(initialElem);
				
				initialElem.setAttribute("generated", "true");
				Element<std::string> transitionElem = _document.createElementNS(_nsInfo.nsURL, "transition");
				_nsInfo.setPrefix(transitionElem);
				
				transitionElem.setAttribute("target", ATTR(initialStates[i], "id"));
				initialElem.appendChild(transitionElem);
				_scxml.appendChild(initialElem);
				initialTransitions.push_back(transitionElem);
			}
		}
	}
	return initialTransitions;
}
	
// a macrostep
InterpreterState InterpreterDraft6::step(bool blocking) {
	try {

		monIter_t monIter;
		NodeSet<std::string> enabledTransitions;
		
		// setup document and interpreter
		if (!_isInitialized)
			init();
		
		// if we failed return false
		if (!_isInitialized)
			return INIT_FAILED;
		
		// run initial transitions
		if (!_stable) {
			stabilize();
			// we might only need a single step
			if (!_running)
				goto EXIT_INTERPRETER;
			return INITIALIZED;
		}
		
		if (!_running)
			return FINISHED;
		
		// read an external event and react
		if (blocking) {
			// wait until an event becomes available
			while(_externalQueue.isEmpty()) {
				_condVar.wait(_mutex);
			}
		} else {
			// return immediately if external queue is empty
			if (_externalQueue.isEmpty())
				return NOTHING_TODO;
		}
		_currEvent = _externalQueue.pop();

	#if VERBOSE
		std::cout << "Received externalEvent event " << _currEvent.name << std::endl;
		if (_running && _currEvent.name == "unblock.and.die") {
			std::cout << "Still running " << this << std::endl;
		} else {
			std::cout << "Aborting " << this << std::endl;
		}
	#endif
		_currEvent.eventType = Event::EXTERNAL; // make sure it is set to external

		// when we were blocking on destructor invocation
		if (!_running) {
			goto EXIT_INTERPRETER;
			return INTERRUPTED;
		}
		// --- MONITOR: beforeProcessingEvent ------------------------------
		for(monIter_t monIter = _monitors.begin(); monIter != _monitors.end(); monIter++) {
			try {
				(*monIter)->beforeProcessingEvent(shared_from_this(), _currEvent);
			}
			USCXML_MONITOR_CATCH_BLOCK(beforeProcessingEvent)
		}
		
		if (iequals(_currEvent.name, "cancel.invoke." + _sessionId))
			return INTERRUPTED;
		
		try {
			_dataModel.setEvent(_currEvent);
		} catch (Event e) {
			LOG(ERROR) << "Syntax error while setting external event:" << std::endl << e << std::endl << _currEvent;
		}

		for (std::map<std::string, Invoker>::iterator invokeIter = _invokers.begin();
				 invokeIter != _invokers.end();
				 invokeIter++) {
			if (iequals(invokeIter->first, _currEvent.invokeid)) {
				Arabica::XPath::NodeSet<std::string> finalizes = filterChildElements(_nsInfo.xmlNSPrefix + "finalize", invokeIter->second.getElement());
				for (int k = 0; k < finalizes.size(); k++) {
					Element<std::string> finalizeElem = Element<std::string>(finalizes[k]);
					executeContent(finalizeElem);
				}
			}
			if (HAS_ATTR(invokeIter->second.getElement(), "autoforward") && DOMUtils::attributeIsTrue(ATTR(invokeIter->second.getElement(), "autoforward"))) {
				try {
					// do not autoforward to invokers that send to #_parent from the SCXML IO Processor!
					// Yes do so, see test229!
					// if (!boost::equals(_currEvent.getOriginType(), "http://www.w3.org/TR/scxml/#SCXMLEventProcessor"))
					invokeIter->second.send(_currEvent);
				} catch(...) {
					LOG(ERROR) << "Exception caught while sending event to invoker " << invokeIter->first;
				}
			}
		}

		
		// run internal processing until we reach a stable configuration again
		enabledTransitions = selectTransitions(_currEvent.name);
		if (!enabledTransitions.empty()) {
			// test 403b
			enabledTransitions.to_document_order();
			microstep(enabledTransitions);
		}

		stabilize();
		return PROCESSED;
		
	EXIT_INTERPRETER:
		if (!_running) {
			// --- MONITOR: beforeCompletion ------------------------------
			for(monIter_t monIter = _monitors.begin(); monIter != _monitors.end(); monIter++) {
				try {
					(*monIter)->beforeCompletion(shared_from_this());
				}
				USCXML_MONITOR_CATCH_BLOCK(beforeCompletion)
			}
			
			exitInterpreter();
			if (_sendQueue) {
				std::map<std::string, std::pair<InterpreterImpl*, SendRequest> >::iterator sendIter = _sendIds.begin();
				while(sendIter != _sendIds.end()) {
					_sendQueue->cancelEvent(sendIter->first);
					sendIter++;
				}
			}
			
			// --- MONITOR: afterCompletion ------------------------------
			for(monIter_t monIter = _monitors.begin(); monIter != _monitors.end(); monIter++) {
				try {
					(*monIter)->afterCompletion(shared_from_this());
				}
				USCXML_MONITOR_CATCH_BLOCK(afterCompletion)
			}
			return FINISHED;
		}
		
		assert(hasLegalConfiguration());
		_mutex.unlock();

		// remove datamodel
		if(_dataModel)
			_dataModel = DataModel();

		return PROCESSED;
		
	} catch (boost::bad_weak_ptr e) {
		LOG(ERROR) << "Unclean shutdown " << std::endl << std::endl;
		return INTERRUPTED;
	}
	
	// set datamodel to null from this thread
	if(_dataModel)
		_dataModel = DataModel();

}

// process transitions until we are in a stable configuration again
void InterpreterDraft6::stabilize() {

	monIter_t monIter;
	NodeSet<std::string> enabledTransitions;
	_stable = false;
	
	if (_configuration.size() == 0) {
		// goto initial configuration
		NodeSet<std::string> initialTransitions = getDocumentInitialTransitions();
		assert(initialTransitions.size() > 0);
		enterStates(initialTransitions);
	}
	
	do { // process microsteps for enabled transitions until there are no more left

		enabledTransitions = selectEventlessTransitions();
		
		if (enabledTransitions.size() == 0) {
			if (_internalQueue.size() == 0) {
				_stable = true;
			} else {
				_currEvent = _internalQueue.front();
				_internalQueue.pop_front();
#if VERBOSE
				std::cout << "Received internal event " << _currEvent.name << std::endl;
#endif
				
				// --- MONITOR: beforeProcessingEvent ------------------------------
				for(monIter_t monIter = _monitors.begin(); monIter != _monitors.end(); monIter++) {
					try {
						(*monIter)->beforeProcessingEvent(shared_from_this(), _currEvent);
					}
					USCXML_MONITOR_CATCH_BLOCK(beforeProcessingEvent)
				}
				
				if (_dataModel)
					_dataModel.setEvent(_currEvent);
				enabledTransitions = selectTransitions(_currEvent.name);
			}
		}
		
		if (!enabledTransitions.empty()) {
			// test 403b
			enabledTransitions.to_document_order();
			microstep(enabledTransitions);
		}
	} while(!_internalQueue.empty() || !_stable);
	
	monIter = _monitors.begin();
	
	// --- MONITOR: onStableConfiguration ------------------------------
	for(monIter_t monIter = _monitors.begin(); monIter != _monitors.end(); monIter++) {
		try {
			(*monIter)->onStableConfiguration(shared_from_this());
		}
		USCXML_MONITOR_CATCH_BLOCK(onStableConfiguration)
	}

	// when we reach a stable configuration, invoke
	for (unsigned int i = 0; i < _statesToInvoke.size(); i++) {
		NodeSet<std::string> invokes = filterChildElements(_nsInfo.xmlNSPrefix + "invoke", _statesToInvoke[i]);
		for (unsigned int j = 0; j < invokes.size(); j++) {
			if (!HAS_ATTR(invokes[j], "persist") || !DOMUtils::attributeIsTrue(ATTR(invokes[j], "persist"))) {
				invoke(invokes[j]);
			}
		}
	}
	_statesToInvoke = NodeSet<std::string>();

}

#if 0
void InterpreterDraft6::mainEventLoop() {
	monIter_t monIter;

	while(_running) {
		NodeSet<std::string> enabledTransitions;
		_stable = false;

		// Here we handle eventless transitions and transitions
		// triggered by internal events until machine is stable
		while(_running && !_stable) {
#if VERBOSE
			std::cout << "Configuration: ";
			for (int i = 0; i < _configuration.size(); i++) {
				std::cout << ATTR(_configuration[i], "id") << ", ";
			}
			std::cout << std::endl;
#endif

			enabledTransitions = selectEventlessTransitions();
			if (enabledTransitions.size() == 0) {
				if (_internalQueue.size() == 0) {
					_stable = true;
				} else {
					_currEvent = _internalQueue.front();
					_internalQueue.pop_front();
#if VERBOSE
					std::cout << "Received internal event " << _currEvent.name << std::endl;
#endif

					// --- MONITOR: beforeProcessingEvent ------------------------------
					for(monIter_t monIter = _monitors.begin(); monIter != _monitors.end(); monIter++) {
						try {
							(*monIter)->beforeProcessingEvent(shared_from_this(), _currEvent);
						}
						USCXML_MONITOR_CATCH_BLOCK(beforeProcessingEvent)
					}

					if (_dataModel)
						_dataModel.setEvent(_currEvent);
					enabledTransitions = selectTransitions(_currEvent.name);
				}
			}
			if (!enabledTransitions.empty()) {
				// test 403b
				enabledTransitions.to_document_order();
				microstep(enabledTransitions);
			}
		}

		for (unsigned int i = 0; i < _statesToInvoke.size(); i++) {
			NodeSet<std::string> invokes = filterChildElements(_nsInfo.xmlNSPrefix + "invoke", _statesToInvoke[i]);
			for (unsigned int j = 0; j < invokes.size(); j++) {
				if (!HAS_ATTR(invokes[j], "persist") || !DOMUtils::attributeIsTrue(ATTR(invokes[j], "persist"))) {
					invoke(invokes[j]);
				}
			}
		}
		_statesToInvoke = NodeSet<std::string>();

		if (!_internalQueue.empty())
			continue;

		// assume that we have a legal configuration as soon as the internal queue is empty
		assert(hasLegalConfiguration());

		monIter = _monitors.begin();

		// --- MONITOR: onStableConfiguration ------------------------------
		for(monIter_t monIter = _monitors.begin(); monIter != _monitors.end(); monIter++) {
			try {
				(*monIter)->onStableConfiguration(shared_from_this());
			}
			USCXML_MONITOR_CATCH_BLOCK(onStableConfiguration)
		}

		_mutex.unlock();
		
		// whenever we have a stable configuration, run the mainThread hooks with 200fps
		while(_externalQueue.isEmpty() && _thread == NULL) {
			runOnMainThread(200);
		}
		_mutex.lock();

		while(_externalQueue.isEmpty()) {
			_condVar.wait(_mutex);
		}
		_currEvent = _externalQueue.pop();
#if VERBOSE
		std::cout << "Received externalEvent event " << _currEvent.name << std::endl;
		if (_running && _currEvent.name == "unblock.and.die") {
			std::cout << "Still running " << this << std::endl;
		} else {
			std::cout << "Aborting " << this << std::endl;
		}
#endif
		_currEvent.eventType = Event::EXTERNAL; // make sure it is set to external
		if (!_running)
			goto EXIT_INTERPRETER;

		// --- MONITOR: beforeProcessingEvent ------------------------------
		for(monIter_t monIter = _monitors.begin(); monIter != _monitors.end(); monIter++) {
			try {
				(*monIter)->beforeProcessingEvent(shared_from_this(), _currEvent);
			}
			USCXML_MONITOR_CATCH_BLOCK(beforeProcessingEvent)
		}

		if (_dataModel && iequals(_currEvent.name, "cancel.invoke." + _sessionId))
			break;

		if (_dataModel) {
			try {
				_dataModel.setEvent(_currEvent);
			} catch (Event e) {
				LOG(ERROR) << "Syntax error while setting external event:" << std::endl << e << std::endl << _currEvent;
			}
		}
		for (std::map<std::string, Invoker>::iterator invokeIter = _invokers.begin();
		        invokeIter != _invokers.end();
		        invokeIter++) {
			if (iequals(invokeIter->first, _currEvent.invokeid)) {
				Arabica::XPath::NodeSet<std::string> finalizes = filterChildElements(_nsInfo.xmlNSPrefix + "finalize", invokeIter->second.getElement());
				for (int k = 0; k < finalizes.size(); k++) {
					Element<std::string> finalizeElem = Element<std::string>(finalizes[k]);
					executeContent(finalizeElem);
				}
			}
			if (HAS_ATTR(invokeIter->second.getElement(), "autoforward") && DOMUtils::attributeIsTrue(ATTR(invokeIter->second.getElement(), "autoforward"))) {
				try {
					// do not autoforward to invokers that send to #_parent from the SCXML IO Processor!
					// Yes do so, see test229!
					// if (!boost::equals(_currEvent.getOriginType(), "http://www.w3.org/TR/scxml/#SCXMLEventProcessor"))
					invokeIter->second.send(_currEvent);
				} catch(...) {
					LOG(ERROR) << "Exception caught while sending event to invoker " << invokeIter->first;
				}
			}
		}
		enabledTransitions = selectTransitions(_currEvent.name);
		if (!enabledTransitions.empty()) {
			// test 403b
			enabledTransitions.to_document_order();
			microstep(enabledTransitions);
		}
	}

EXIT_INTERPRETER:
	// --- MONITOR: beforeCompletion ------------------------------
	for(monIter_t monIter = _monitors.begin(); monIter != _monitors.end(); monIter++) {
		try {
			(*monIter)->beforeCompletion(shared_from_this());
		}
		USCXML_MONITOR_CATCH_BLOCK(beforeCompletion)
	}

	exitInterpreter();
	if (_sendQueue) {
		std::map<std::string, std::pair<InterpreterImpl*, SendRequest> >::iterator sendIter = _sendIds.begin();
		while(sendIter != _sendIds.end()) {
			_sendQueue->cancelEvent(sendIter->first);
			sendIter++;
		}
	}

	// --- MONITOR: afterCompletion ------------------------------
	for(monIter_t monIter = _monitors.begin(); monIter != _monitors.end(); monIter++) {
		try {
			(*monIter)->afterCompletion(shared_from_this());
		}
		USCXML_MONITOR_CATCH_BLOCK(afterCompletion)
	}

}
#endif
	
Arabica::XPath::NodeSet<std::string> InterpreterDraft6::selectTransitions(const std::string& event) {
	Arabica::XPath::NodeSet<std::string> enabledTransitions;

	NodeSet<std::string> states;
	for (unsigned int i = 0; i < _configuration.size(); i++) {
		if (isAtomic(_configuration[i]))
			states.push_back(_configuration[i]);
	}
	states.to_document_order();

#if 0
	std::cout << "Atomic states: " << std::endl;
	for (int i = 0; i < states.size(); i++) {
		std::cout << states[i] << std::endl << "----" << std::endl;
	}
	std::cout << std::endl;
#endif

	unsigned int index = 0;
	while(states.size() > index) {
		bool foundTransition = false;
		NodeSet<std::string> transitions = filterChildElements(_nsInfo.xmlNSPrefix + "transition", states[index]);
		for (unsigned int k = 0; k < transitions.size(); k++) {
			if (isEnabledTransition(transitions[k], event)) {
				enabledTransitions.push_back(transitions[k]);
				foundTransition = true;
				goto LOOP;
			}
		}
		if (!foundTransition) {
			Node<std::string> parent = states[index].getParentNode();
			if (parent) {
				states.push_back(parent);
			}
		}
LOOP:
		index++;
	}

	enabledTransitions = filterPreempted(enabledTransitions);

#if 0
	std::cout << "Enabled transitions: " << std::endl;
	for (int i = 0; i < enabledTransitions.size(); i++) {
		std::cout << DOMUtils::xPathForNode(enabledTransitions[i]) << std::endl;
	}
	std::cout << std::endl;
#endif

	return enabledTransitions;
}

bool InterpreterDraft6::isEnabledTransition(const Node<std::string>& transition, const std::string& event) {
	std::string eventName;
	if (HAS_ATTR(transition, "event")) {
		eventName = ATTR(transition, "event");
	} else if(HAS_ATTR(transition, "eventexpr")) {
		if (_dataModel) {
			eventName = _dataModel.evalAsString(ATTR(transition, "eventexpr"));
		} else {
			LOG(ERROR) << "Transition has eventexpr attribute with no datamodel defined";
			return false;
		}
	} else {
		return false;
	}

	std::list<std::string> eventNames = tokenizeIdRefs(eventName);
	std::list<std::string>::iterator eventIter = eventNames.begin();
	while(eventIter != eventNames.end()) {
		if(nameMatch(*eventIter, event) && hasConditionMatch(transition)) {
			return true;
		}
		eventIter++;
	}
	return false;
}

Arabica::XPath::NodeSet<std::string> InterpreterDraft6::selectEventlessTransitions() {
	Arabica::XPath::NodeSet<std::string> enabledTransitions;

	NodeSet<std::string> states;
	for (unsigned int i = 0; i < _configuration.size(); i++) {
		if (isAtomic(_configuration[i]))
			states.push_back(_configuration[i]);
	}
	states.to_document_order();

#if 0
	std::cout << "Atomic States: ";
	for (int i = 0; i < atomicStates.size(); i++) {
		std::cout << ATTR(atomicStates[i], "id") << ", ";
	}
	std::cout << std::endl;
#endif

	unsigned int index = 0;
	while(states.size() > index) {
		bool foundTransition = false;
		NodeSet<std::string> transitions = filterChildElements(_nsInfo.xmlNSPrefix + "transition", states[index]);
		for (unsigned int k = 0; k < transitions.size(); k++) {
			if (!HAS_ATTR(transitions[k], "event") && hasConditionMatch(transitions[k])) {
				enabledTransitions.push_back(transitions[k]);
				foundTransition = true;
				goto LOOP;
			}
		}
		if (!foundTransition) {
			Node<std::string> parent = states[index].getParentNode();
			if (parent) {
				states.push_back(parent);
			}
		}
LOOP:
		index++;
	}

#if 0
	std::cout << "Enabled eventless transitions: " << std::endl;
	for (int i = 0; i < enabledTransitions.size(); i++) {
		std::cout << enabledTransitions[i] << std::endl << "----" << std::endl;
	}
	std::cout << std::endl;
#endif

	enabledTransitions = filterPreempted(enabledTransitions);
	return enabledTransitions;
}

Arabica::XPath::NodeSet<std::string> InterpreterDraft6::filterPreempted(const Arabica::XPath::NodeSet<std::string>& enabledTransitions) {
	Arabica::XPath::NodeSet<std::string> filteredTransitions;
	for (unsigned int i = 0; i < enabledTransitions.size(); i++) {
		Node<std::string> t = enabledTransitions[i];
		if (!isTargetless(t)) {
			for (unsigned int j = 0; j < filteredTransitions.size(); j++) {
				if (j == i)
					continue;
				Node<std::string> t2 = filteredTransitions[j];
				if (isPreemptingTransition(t2, t)) {
#if 0
					std::cout << "#####" << std::endl << "Transition " << std::endl
					          << t2 << std::endl << " preempts " << std::endl << t << std::endl << "#####" << std::endl;
#endif
					goto LOOP;
				}
			}
		}
#if 0
		std::cout << "----" << "Enabling Transition " << std::endl << t << std::endl;
#endif

		filteredTransitions.push_back(t);
LOOP:
		;
	}
	return filteredTransitions;
}



/**
 * Is t1 preempting t2?
 */
bool InterpreterDraft6::isPreemptingTransition(const Node<std::string>& t1, const Node<std::string>& t2) {
	assert(t1);
	assert(t2);

#if 0
	std::cout << "Checking preemption: " << std::endl << t1 << std::endl << t2 << std::endl;
#endif

	if (t1 == t2)
		return false;
	if (isTargetless(t1))
		return false; // targetless transitions do not preempt any other transitions
	if (isWithinParallel(t1) && isCrossingBounds(t2))
		return true; // transitions within a single child of <parallel> preempt transitions that cross child boundaries
	if (isCrossingBounds(t1))
		return true; // transitions that cross child boundaries preempt all other transitions

	return false;
}

bool InterpreterDraft6::isCrossingBounds(const Node<std::string>& transition) {
	if (!isTargetless(transition) && !isWithinParallel(transition))
		return true;
	return false;
}

bool InterpreterDraft6::isWithinParallel(const Node<std::string>& transition) {
	if (isTargetless(transition))
		return false;

	Node<std::string> source;
	if (HAS_ATTR(transition, "type") && iequals(ATTR(transition, "type"), "internal")) {
		source = getSourceState(transition);
	} else {
		source = getSourceState(transition).getParentNode();
	}
	NodeSet<std::string> targets = getTargetStates(transition);
	targets.push_back(source);

	Node<std::string> lcpa = findLCPA(targets);
	return lcpa;
}

Node<std::string> InterpreterDraft6::findLCPA(const Arabica::XPath::NodeSet<std::string>& states) {
	Arabica::XPath::NodeSet<std::string> ancestors = getProperAncestors(states[0], Node<std::string>());
	Node<std::string> ancestor;
	for (int i = 0; i < ancestors.size(); i++) {
		if (!isParallel(ancestors[i]))
			continue;
		for (int j = 0; j < states.size(); j++) {
			if (!isDescendant(states[j], ancestors[i]) && (states[j] != ancestors[i]))
				goto NEXT_ANCESTOR;
		}
		ancestor = ancestors[i];
		break;
NEXT_ANCESTOR:
		;
	}
	return ancestor;
}

void InterpreterDraft6::microstep(const Arabica::XPath::NodeSet<std::string>& enabledTransitions) {
#if VERBOSE
	std::cout << "Transitions: ";
	for (int i = 0; i < enabledTransitions.size(); i++) {
		std::cout << ((Element<std::string>)getSourceState(enabledTransitions[i])).getAttribute("id") << " -> " << std::endl;
		NodeSet<std::string> targetSet = getTargetStates(enabledTransitions[i]);
		for (int j = 0; j < targetSet.size(); j++) {
			std::cout << "    " << ((Element<std::string>)targetSet[j]).getAttribute("id") << std::endl;
		}
	}
	std::cout << std::endl;
#endif

	// --- MONITOR: beforeMicroStep ------------------------------
	for(monIter_t monIter = _monitors.begin(); monIter != _monitors.end(); monIter++) {
		try {
			(*monIter)->beforeMicroStep(shared_from_this());
		}
		USCXML_MONITOR_CATCH_BLOCK(beforeMicroStep)
	}

	exitStates(enabledTransitions);

	monIter_t monIter;
	for (int i = 0; i < enabledTransitions.size(); i++) {
		Element<std::string> transition(enabledTransitions[i]);

		// --- MONITOR: beforeTakingTransitions ------------------------------
		for(monIter_t monIter = _monitors.begin(); monIter != _monitors.end(); monIter++) {
			try {
				(*monIter)->beforeTakingTransition(shared_from_this(), transition, (i + 1 < enabledTransitions.size()));
			}
			USCXML_MONITOR_CATCH_BLOCK(beforeTakingTransitions)
		}

		executeContent(transition);

		// --- MONITOR: afterTakingTransitions ------------------------------
		for(monIter_t monIter = _monitors.begin(); monIter != _monitors.end(); monIter++) {
			try {
				(*monIter)->afterTakingTransition(shared_from_this(), transition, (i + 1 < enabledTransitions.size()));
			}
			USCXML_MONITOR_CATCH_BLOCK(afterTakingTransitions)
		}
	}

	enterStates(enabledTransitions);

	// --- MONITOR: afterMicroStep ------------------------------
	for(monIter_t monIter = _monitors.begin(); monIter != _monitors.end(); monIter++) {
		try {
			(*monIter)->afterMicroStep(shared_from_this());
		}
		USCXML_MONITOR_CATCH_BLOCK(afterMicroStep)
	}

}

void InterpreterDraft6::exitInterpreter() {
#if VERBOSE
	std::cout << "Exiting interpreter " << _name << std::endl;
#endif
	NodeSet<std::string> statesToExit = _configuration;
	statesToExit.forward(false);
	statesToExit.sort();

	for (int i = 0; i < statesToExit.size(); i++) {
		Arabica::XPath::NodeSet<std::string> onExitElems = filterChildElements(_nsInfo.xmlNSPrefix + "onexit", statesToExit[i]);
		for (int j = 0; j < onExitElems.size(); j++) {
			executeContent(onExitElems[j]);
		}
		Arabica::XPath::NodeSet<std::string> invokeElems = filterChildElements(_nsInfo.xmlNSPrefix + "invoke", statesToExit[i]);
		// TODO: we ought to cancel all remaining invokers just to be sure with the persist extension
		for (int j = 0; j < invokeElems.size(); j++) {
			cancelInvoke(invokeElems[j]);
		}
		if (isFinal(statesToExit[i]) && parentIsScxmlState(statesToExit[i])) {
			returnDoneEvent(statesToExit[i]);
		}
	}
	_configuration = NodeSet<std::string>();
}


void InterpreterDraft6::exitStates(const Arabica::XPath::NodeSet<std::string>& enabledTransitions) {
	NodeSet<std::string> statesToExit;
	monIter_t monIter;

#if VERBOSE
	std::cout << _name << ": Enabled exit transitions: " << std::endl;
	for (int i = 0; i < enabledTransitions.size(); i++) {
		std::cout << enabledTransitions[i] << std::endl;
	}
	std::cout << std::endl;
#endif

	for (int i = 0; i < enabledTransitions.size(); i++) {
		Element<std::string> t = ((Element<std::string>)enabledTransitions[i]);
		if (!isTargetless(t)) {
			Node<std::string> ancestor;
			Node<std::string> source = getSourceState(t);
//			std::cout << t << std::endl << TAGNAME(t) << std::endl;
			NodeSet<std::string> tStates = getTargetStates(t);
			bool isInternal = (HAS_ATTR(t, "type") && iequals(ATTR(t, "type"), "internal")); // external is default
			bool allDescendants = true;
			for (int j = 0; j < tStates.size(); j++) {
				if (!isDescendant(tStates[j], source)) {
					allDescendants = false;
					break;
				}
			}
			if (isInternal && allDescendants && isCompound(source)) {
				ancestor = source;
			} else {
				NodeSet<std::string> tmpStates;
				tmpStates.push_back(source);
				tmpStates.insert(tmpStates.end(), tStates.begin(), tStates.end());
#if VERBOSE
				std::cout << _name << ": tmpStates: ";
				for (int i = 0; i < tmpStates.size(); i++) {
					std::cout << ATTR(tmpStates[i], "id") << ", ";
				}
				std::cout << std::endl;
#endif
				ancestor = findLCCA(tmpStates);
			}
#if VERBOSE
			std::cout << _name << ": Ancestor: " << ATTR(ancestor, "id") << std::endl;;
#endif
			for (int j = 0; j < _configuration.size(); j++) {
				if (isDescendant(_configuration[j], ancestor))
					statesToExit.push_back(_configuration[j]);
			}
		}
	}
	// remove statesToExit from _statesToInvoke
	std::list<Node<std::string> > tmp;
	for (int i = 0; i < _statesToInvoke.size(); i++) {
		if (!isMember(_statesToInvoke[i], statesToExit)) {
			tmp.push_back(_statesToInvoke[i]);
		}
	}
	_statesToInvoke = NodeSet<std::string>();
	_statesToInvoke.insert(_statesToInvoke.end(), tmp.begin(), tmp.end());

	statesToExit.forward(false);
	statesToExit.sort();

#if VERBOSE
	std::cout << _name << ": States to exit: ";
	for (int i = 0; i < statesToExit.size(); i++) {
		std::cout << LOCALNAME(statesToExit[i]) << ":" << ATTR(statesToExit[i], "id") << ", ";
	}
	std::cout << std::endl;
#endif

	for (int i = 0; i < statesToExit.size(); i++) {
		NodeSet<std::string> histories = filterChildElements(_nsInfo.xmlNSPrefix + "history", statesToExit[i]);
		for (int j = 0; j < histories.size(); j++) {
			Element<std::string> historyElem = (Element<std::string>)histories[j];
			std::string historyType = (historyElem.hasAttribute("type") ? historyElem.getAttribute("type") : "shallow");
			NodeSet<std::string> historyNodes;
			for (int k = 0; k < _configuration.size(); k++) {
				if (iequals(historyType, "deep")) {
					if (isAtomic(_configuration[k]) && isDescendant(_configuration[k], statesToExit[i]))
						historyNodes.push_back(_configuration[k]);
				} else {
					if (_configuration[k].getParentNode() == statesToExit[i])
						historyNodes.push_back(_configuration[k]);
				}
			}
			_historyValue[historyElem.getAttribute("id")] = historyNodes;
#if VERBOSE
			std::cout << _name << ": History node " << ATTR(historyElem, "id") << " contains: ";
			for (int i = 0; i < historyNodes.size(); i++) {
				std::cout << ATTR(historyNodes[i], "id") << ", ";
			}
			std::cout << std::endl;
#endif

		}
	}

	for (int i = 0; i < statesToExit.size(); i++) {
		// --- MONITOR: beforeExitingState ------------------------------
		for(monIter_t monIter = _monitors.begin(); monIter != _monitors.end(); monIter++) {
			try {
				(*monIter)->beforeExitingState(shared_from_this(), Element<std::string>(statesToExit[i]), (i + 1 < statesToExit.size()));
			}
			USCXML_MONITOR_CATCH_BLOCK(beforeExitingState)
		}

		NodeSet<std::string> onExits = filterChildElements(_nsInfo.xmlNSPrefix + "onExit", statesToExit[i]);
		for (int j = 0; j < onExits.size(); j++) {
			Element<std::string> onExitElem = (Element<std::string>)onExits[j];
			executeContent(onExitElem);
		}

		// --- MONITOR: afterExitingState ------------------------------
		for(monIter_t monIter = _monitors.begin(); monIter != _monitors.end(); monIter++) {
			try {
				(*monIter)->afterExitingState(shared_from_this(), Element<std::string>(statesToExit[i]), (i + 1 < statesToExit.size()));
			}
			USCXML_MONITOR_CATCH_BLOCK(afterExitingState)
		}

		NodeSet<std::string> invokes = filterChildElements(_nsInfo.xmlNSPrefix + "invoke", statesToExit[i]);
		for (int j = 0; j < invokes.size(); j++) {
			Element<std::string> invokeElem = (Element<std::string>)invokes[j];
			if (HAS_ATTR(invokeElem, "persist") && DOMUtils::attributeIsTrue(ATTR(invokeElem, "persist"))) {
				// extension for flattened SCXML documents, we will need an explicit uninvoke element
			} else {
				cancelInvoke(invokeElem);
			}
		}

		// remove statesToExit[i] from _configuration - test409
		tmp.clear();
		for (int j = 0; j < _configuration.size(); j++) {
			if (_configuration[j] != statesToExit[i]) {
				tmp.push_back(_configuration[j]);
			}
		}
		_configuration = NodeSet<std::string>();
		_configuration.insert(_configuration.end(), tmp.begin(), tmp.end());
	}
}

void InterpreterDraft6::enterStates(const Arabica::XPath::NodeSet<std::string>& enabledTransitions) {
	NodeSet<std::string> statesToEnter;
	NodeSet<std::string> statesForDefaultEntry;
	monIter_t monIter;

#if VERBOSE
	std::cout << _name << ": Enabled enter transitions: " << std::endl;
	for (int i = 0; i < enabledTransitions.size(); i++) {
		std::cout << "\t" << enabledTransitions[i] << std::endl;
	}
	std::cout << std::endl;
#endif

	for (int i = 0; i < enabledTransitions.size(); i++) {
		Element<std::string> transition = ((Element<std::string>)enabledTransitions[i]);
		if (!isTargetless(transition)) {
			std::string transitionType = (iequals(transition.getAttribute("type"), "internal") ? "internal" : "external");
			NodeSet<std::string> tStates = getTargetStates(transition);

#if VERBOSE
			std::cout << _name << ": Target States: ";
			for (int i = 0; i < tStates.size(); i++) {
				std::cout << ATTR(tStates[i], "id") << ", ";
			}
			std::cout << std::endl;
#endif

			Node<std::string> ancestor;
			Node<std::string> source = getSourceState(transition);
#if VERBOSE
			std::cout << _name << ": Source States: " << ATTR(source, "id") << std::endl;
#endif
			assert(source);

			bool allDescendants = true;
			for (int j = 0; j < tStates.size(); j++) {
				if (!isDescendant(tStates[j], source)) {
					allDescendants = false;
					break;
				}
			}
			if (iequals(transitionType, "internal") &&
			        isCompound(source) &&
			        allDescendants) {
				ancestor = source;
			} else {
				NodeSet<std::string> tmpStates;
				tmpStates.push_back(source);
				tmpStates.insert(tmpStates.end(), tStates.begin(), tStates.end());

				ancestor = findLCCA(tmpStates);
			}

#if VERBOSE
			std::cout << _name << ": Ancestor: " << ATTR(ancestor, "id") << std::endl;
#endif

			for (int j = 0; j < tStates.size(); j++) {
				addStatesToEnter(tStates[j], statesToEnter, statesForDefaultEntry);
			}

#if VERBOSE
			std::cout << _name << ": States to enter: ";
			for (int i = 0; i < statesToEnter.size(); i++) {
				std::cout << LOCALNAME(statesToEnter[i]) << ":" << ATTR(statesToEnter[i], "id") << ", ";
			}
			std::cout << std::endl;
#endif

			for (int j = 0; j < tStates.size(); j++) {
				NodeSet<std::string> ancestors = getProperAncestors(tStates[j], ancestor);

#if VERBOSE
				std::cout << _name << ": Proper Ancestors of " << ATTR(tStates[j], "id") << " and " << ATTR(ancestor, "id") << ": ";
				for (int i = 0; i < ancestors.size(); i++) {
					std::cout << ATTR(ancestors[i], "id") << ", ";
				}
				std::cout << std::endl;
#endif

				for (int k = 0; k < ancestors.size(); k++) {
					statesToEnter.push_back(ancestors[k]);
					if(isParallel(ancestors[k])) {
						NodeSet<std::string> childs = getChildStates(ancestors[k]);
						for (int l = 0; l < childs.size(); l++) {
							bool someIsDescendant = false;
							for (int m = 0; m < statesToEnter.size(); m++) {
								if (isDescendant(statesToEnter[m], childs[l])) {
									someIsDescendant = true;
									break;
								}
							}
							if (!someIsDescendant) {
								addStatesToEnter(childs[l], statesToEnter, statesForDefaultEntry);
							}
						}
					}
				}
			}
		}
	}
	statesToEnter.to_document_order();

#if VERBOSE
	std::cout << _name << ": States to enter: ";
	for (int i = 0; i < statesToEnter.size(); i++) {
		std::cout << ATTR(statesToEnter[i], "id") << ", ";
	}
	std::cout << std::endl;
#endif

	for (int i = 0; i < statesToEnter.size(); i++) {
		Element<std::string> stateElem = (Element<std::string>)statesToEnter[i];

		// extension for flattened interpreters
		for (unsigned int k = 0; k < statesToEnter.size(); k++) {
			NodeSet<std::string> invokes = filterChildElements(_nsInfo.xmlNSPrefix + "invoke", statesToEnter[k]);
			for (unsigned int j = 0; j < invokes.size(); j++) {
				if (HAS_ATTR(invokes[j], "persist") && DOMUtils::attributeIsTrue(ATTR(invokes[j], "persist"))) {
					invoke(invokes[j]);
				}
			}
		}

		// --- MONITOR: beforeEnteringState ------------------------------
		for(monIter_t monIter = _monitors.begin(); monIter != _monitors.end(); monIter++) {
			try {
				(*monIter)->beforeEnteringState(shared_from_this(), stateElem, (i + 1 < statesToEnter.size()));
			}
			USCXML_MONITOR_CATCH_BLOCK(beforeEnteringState)
		}

		// extension for flattened SCXML documents, we will need an explicit uninvoke element
		NodeSet<std::string> uninvokes = filterChildElements(_nsInfo.xmlNSPrefix + "uninvoke", statesToEnter[i]);
		for (int j = 0; j < uninvokes.size(); j++) {
			Element<std::string> uninvokeElem = (Element<std::string>)uninvokes[j];
			cancelInvoke(uninvokeElem);
		}

		_configuration.push_back(stateElem);
		_statesToInvoke.push_back(stateElem);

//		if (_binding == LATE && stateElem.getAttribute("isFirstEntry").size() > 0) {
		if (_binding == LATE && !isMember(stateElem, _alreadyEntered)) {
			NodeSet<std::string> dataModelElems = filterChildElements(_nsInfo.xmlNSPrefix + "datamodel", stateElem);
			if(dataModelElems.size() > 0 && _dataModel) {
				Arabica::XPath::NodeSet<std::string> dataElems = filterChildElements(_nsInfo.xmlNSPrefix + "data", dataModelElems[0]);
				for (int j = 0; j < dataElems.size(); j++) {
					if (dataElems[j].getNodeType() == Node_base::ELEMENT_NODE)
						initializeData(Element<std::string>(dataElems[j]));
				}
			}
			_alreadyEntered.push_back(stateElem);
//			stateElem.setAttribute("isFirstEntry", "");
		}
		// execute onentry executable content
		NodeSet<std::string> onEntryElems = filterChildElements(_nsInfo.xmlNSPrefix + "onEntry", stateElem);
		executeContent(onEntryElems, false);

		// --- MONITOR: afterEnteringState ------------------------------
		for(monIter_t monIter = _monitors.begin(); monIter != _monitors.end(); monIter++) {
			try {
				(*monIter)->afterEnteringState(shared_from_this(), stateElem, (i + 1 < statesToEnter.size()));
			}
			USCXML_MONITOR_CATCH_BLOCK(afterEnteringState)
		}

		if (isMember(stateElem, statesForDefaultEntry)) {
			// execute initial transition content for compound states
			Arabica::XPath::NodeSet<std::string> transitions = _xpath.evaluate("" + _nsInfo.xpathPrefix + "initial/" + _nsInfo.xpathPrefix + "transition", stateElem).asNodeSet();
			for (int j = 0; j < transitions.size(); j++) {
				executeContent(transitions[j]);
			}
		}

		if (isFinal(stateElem)) {
			internalDoneSend(stateElem);
			Element<std::string> parent = (Element<std::string>)stateElem.getParentNode();

			if (isParallel(parent.getParentNode())) {
				Element<std::string> grandParent = (Element<std::string>)parent.getParentNode();

				Arabica::XPath::NodeSet<std::string> childs = getChildStates(grandParent);
				bool inFinalState = true;
				for (int j = 0; j < childs.size(); j++) {
					if (!isInFinalState(childs[j])) {
						inFinalState = false;
						break;
					}
				}
				if (inFinalState) {
					internalDoneSend(parent);
				}
			}
		}
	}
	for (int i = 0; i < _configuration.size(); i++) {
		Element<std::string> stateElem = (Element<std::string>)_configuration[i];
		if (isFinal(stateElem) && parentIsScxmlState(stateElem)) {
			_running = false;
			_done = true;
		}
	}
}

void InterpreterDraft6::addStatesToEnter(const Node<std::string>& state,
        Arabica::XPath::NodeSet<std::string>& statesToEnter,
        Arabica::XPath::NodeSet<std::string>& statesForDefaultEntry) {
	std::string stateId = ((Element<std::string>)state).getAttribute("id");

#if VERBOSE
	std::cout << "Adding state to enter: " << stateId << std::endl;
#endif
	if (isHistory(state)) {
		if (_historyValue.find(stateId) != _historyValue.end()) {
			Arabica::XPath::NodeSet<std::string> historyValue = _historyValue[stateId];

#if VERBOSE
			std::cout << "History State " << ATTR(state, "id") << ": ";
			for (int i = 0; i < historyValue.size(); i++) {
				std::cout << ATTR(historyValue[i], "id") << ", ";
			}
			std::cout << std::endl;
#endif

			for (int i = 0; i < historyValue.size(); i++) {
				addStatesToEnter(historyValue[i], statesToEnter, statesForDefaultEntry);
				NodeSet<std::string> ancestors = getProperAncestors(historyValue[i], state);

#if VERBOSE
				std::cout << "Proper Ancestors: ";
				for (int i = 0; i < ancestors.size(); i++) {
					std::cout << ATTR(ancestors[i], "id") << ", ";
				}
				std::cout << std::endl;
#endif

				for (int j = 0; j < ancestors.size(); j++) {
					statesToEnter.push_back(ancestors[j]);
				}
			}
		} else {
			NodeSet<std::string> transitions = filterChildElements(_nsInfo.xmlNSPrefix + "transition", state);
			for (int i = 0; i < transitions.size(); i++) {
				NodeSet<std::string> targets = getTargetStates(transitions[i]);
				for (int j = 0; j < targets.size(); j++) {
					addStatesToEnter(targets[j], statesToEnter, statesForDefaultEntry);

					// Modifications from chris nuernberger
					NodeSet<std::string> ancestors = getProperAncestors(targets[j], state);
					for (int k = 0; k < ancestors.size(); k++) {
						statesToEnter.push_back(ancestors[k]);
					}
				}
			}
		}
	} else {
		statesToEnter.push_back(state);
		if (isCompound(state)) {
			statesForDefaultEntry.push_back(state);

			NodeSet<std::string> tStates = getInitialStates(state);
			for (int i = 0; i < tStates.size(); i++) {
				addStatesToEnter(tStates[i], statesToEnter, statesForDefaultEntry);
			}

			//			addStatesToEnter(getInitialState(state), statesToEnter, statesForDefaultEntry);
			//      NodeSet<std::string> tStates = getTargetStates(getInitialState(state));

		} else if(isParallel(state)) {
			NodeSet<std::string> childStates = getChildStates(state);
			for (int i = 0; i < childStates.size(); i++) {
				addStatesToEnter(childStates[i], statesToEnter, statesForDefaultEntry);
			}
		}
	}
}


}