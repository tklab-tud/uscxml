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

#include "InterpreterRC.h"

#include "uscxml/Factory.h"
#include "uscxml/concurrency/eventqueue/DelayedEventQueue.h"

#include <glog/logging.h>
#include "uscxml/UUID.h"
#include "uscxml/DOMUtils.h"

namespace uscxml {

using namespace Arabica::XPath;
using namespace Arabica::DOM;

/**
procedure interpret(doc):
    if not valid(doc): failWithError()
    expandScxmlSource(doc)
    configuration = new OrderedSet()
    statesToInvoke = new OrderedSet()
    internalQueue = new Queue()
    externalQueue = new BlockingQueue()
    historyValue = new HashTable()
    datamodel = new Datamodel(doc)
    if doc.binding == "early":
        initializeDatamodel(datamodel, doc)
    running = true
    executeGlobalScriptElement(doc)
    enterStates([doc.initial.transition])
    mainEventLoop()
 */
InterpreterState InterpreterRC::interpret() {
	try {
		tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
		if (!_isInitialized)
			init();

		//  dump();

		// just make sure we have a session id
		assert(_sessionId.length() > 0);

		setupIOProcessors();

		std::string datamodelName;
		if (datamodelName.length() == 0 && HAS_ATTR(_scxml, "datamodel"))
			datamodelName = ATTR(_scxml, "datamodel");
		if (datamodelName.length() == 0 && HAS_ATTR(_scxml, "profile")) // SCION SCXML uses profile to specify datamodel
			datamodelName = ATTR(_scxml, "profile");
		if(datamodelName.length() > 0) {
			_dataModel = _factory->createDataModel(datamodelName, this);
			if (!_dataModel) {
				Event e;
				e.data.compound["cause"] = Data("Cannot instantiate datamodel", Data::VERBATIM);
				throw e;
			}
		} else {
			_dataModel = _factory->createDataModel("null", this);
		}
		if(datamodelName.length() > 0  && !_dataModel) {
			LOG(ERROR) << "No datamodel for " << datamodelName << " registered";
		}

		if (_dataModel) {
			_dataModel.assign("_x.args", _cmdLineOptions);
		}

		_binding = (HAS_ATTR(_scxml, "binding") && iequals(ATTR(_scxml, "binding"), "late") ? LATE : EARLY);

		// @TODO: Reread http://www.w3.org/TR/scxml/#DataBinding

		if (_dataModel && _binding == EARLY) {
			// initialize all data elements
			NodeSet<std::string> dataElems = _xpath.evaluate("//" + _nsInfo.xpathPrefix + "data", _scxml).asNodeSet();
			for (unsigned int i = 0; i < dataElems.size(); i++) {
				// do not process data elements of nested documents from invokers
				if (!getAncestorElement(dataElems[i], _nsInfo.xmlNSPrefix + "invoke"))
					if (dataElems[i].getNodeType() == Node_base::ELEMENT_NODE) {
						initializeData(Element<std::string>(dataElems[i]));
					}
			}
		} else if(_dataModel) {
			// initialize current data elements
			NodeSet<std::string> topDataElems = filterChildElements(_nsInfo.xmlNSPrefix + "data", filterChildElements(_nsInfo.xmlNSPrefix + "datamodel", _scxml));
			for (unsigned int i = 0; i < topDataElems.size(); i++) {
				if (topDataElems[i].getNodeType() == Node_base::ELEMENT_NODE)
					initializeData(Element<std::string>(topDataElems[i]));
			}
		}

		// executeGlobalScriptElements
		NodeSet<std::string> globalScriptElems = filterChildElements(_nsInfo.xmlNSPrefix + "script", _scxml);
		for (unsigned int i = 0; i < globalScriptElems.size(); i++) {
			if (_dataModel) {
				executeContent(globalScriptElems[i]);
			}
		}

		NodeSet<std::string> initialTransitions;

		if (_startConfiguration.size() > 0) {
			// we emulate entering a given configuration by creating a pseudo deep history
			Element<std::string> initHistory = _document.createElementNS(_nsInfo.nsURL, "history");
			_nsInfo.setPrefix(initHistory);

			initHistory.setAttribute("id", UUID::getUUID());
			initHistory.setAttribute("type", "deep");
			_scxml.insertBefore(initHistory, _scxml.getFirstChild());

			std::string histId = ATTR(initHistory, "id");
			NodeSet<std::string> histStates;
			for (std::list<std::string>::const_iterator stateIter = _startConfiguration.begin(); stateIter != _startConfiguration.end(); stateIter++) {
				histStates.push_back(getState(*stateIter));
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

		assert(initialTransitions.size() > 0);

		enterStates(initialTransitions);
		//	_mutex.unlock();

		//  assert(hasLegalConfiguration());
		mainEventLoop();
	} catch (boost::bad_weak_ptr e) {
		LOG(ERROR) << "Unclean shutdown " << std::endl << std::endl;
	}
	// set datamodel to null from this thread
	if(_dataModel)
		_dataModel = DataModel();

	return _state;
}

/**
procedure mainEventLoop():
    while running:
        enabledTransitions = null
        macrostepDone = false
        # Here we handle eventless transitions and transitions
        # triggered by internal events until macrostep is complete
        while running and not macrostepDone:
            enabledTransitions = selectEventlessTransitions()
            if enabledTransitions.isEmpty():
                if internalQueue.isEmpty():
                    macrostepDone = true
                else:
                    internalEvent = internalQueue.dequeue()
                    datamodel["_event"] = internalEvent
                    enabledTransitions = selectTransitions(internalEvent)
            if not enabledTransitions.isEmpty():
                microstep(enabledTransitions.toList())
        # either we're in a final state, and we break out of the loop
        if not running:
            break;
        # or we've completed a macrostep, so we start a new macrostep by waiting for an external event
        # Here we invoke whatever needs to be invoked. The implementation of 'invoke' is platform-specific
        for state in statesToInvoke:
            for inv in state.invoke:
                invoke(inv)
        statesToInvoke.clear()
        # Invoking may have raised internal error events and we iterate to handle them
        if not internalQueue.isEmpty():
            continue
       # A blocking wait for an external event.  Alternatively, if we have been invoked
       # our parent session also might cancel us.  The mechanism for this is platform specific,
       # but here we assume it's a special event we receive
       externalEvent = externalQueue.dequeue()
       if isCancelEvent(externalEvent):
           running = false
           continue
       datamodel["_event"] = externalEvent
       for state in configuration:
           for inv in state.invoke:
              if inv.invokeid == externalEvent.invokeid:
                  applyFinalize(inv, externalEvent)
              if inv.autoforward:
                  send(inv.id, externalEvent)
       enabledTransitions = selectTransitions(externalEvent)
       if not enabledTransitions.isEmpty():
           microstep(enabledTransitions.toList())
    # End of outer while running loop.  If we get here, we have reached a top-level final state or have been cancelled
    exitInterpreter()
 */
void InterpreterRC::mainEventLoop() {

	while(_running) {
		NodeSet<std::string> enabledTransitions;
		_stable = false;

		// Here we handle eventless transitions and transitions
		// triggered by internal events until machine is stable
		while(_running && !_stable) {

			enabledTransitions = selectEventlessTransitions();
			if (enabledTransitions.size() == 0) {
				if (_internalQueue.size() == 0) {
					_stable = true;
				} else {
					_currEvent = _internalQueue.front();
					_internalQueue.pop_front();

					USCXML_MONITOR_CALLBACK2(beforeProcessingEvent, _currEvent)

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

		if (!_running)
			goto EXIT_INTERPRETER;

		for (unsigned int i = 0; i < _statesToInvoke.size(); i++) {
			NodeSet<std::string> invokes = filterChildElements(_nsInfo.xmlNSPrefix + "invoke", _statesToInvoke[i]);
			for (unsigned int j = 0; j < invokes.size(); j++) {
				invoke(invokes[j]);
			}
		}
		_statesToInvoke = NodeSet<std::string>();

		if (!_internalQueue.empty())
			continue;

		// assume that we have a legal configuration as soon as the internal queue is empty
		if (!hasLegalConfiguration()) {
			std::cout << "Illegal configuration!" << std::endl;
			for (unsigned int j = 0; j < _configuration.size(); j++) {
				std::cout << ATTR(_configuration[j], "id") << " ";
			}
			std::cout << std::endl;
		}
		assert(hasLegalConfiguration());

		//    if (!_sendQueue || _sendQueue->isEmpty()) {

		USCXML_MONITOR_CALLBACK(onStableConfiguration)

		//    }

		_mutex.unlock();
		// whenever we have a stable configuration, run the mainThread hooks with 200fps
		while(_externalQueue.isEmpty() && _thread == NULL) {
			runOnMainThread(200);
		}
		_mutex.lock();

		// A blocking wait for an external event.  Alternatively, if we have been invoked
		// our parent session also might cancel us.  The mechanism for this is platform specific,
		// but here we assume it's a special event we receive

		while(_externalQueue.isEmpty()) {
			_condVar.wait(_mutex);
		}
		_currEvent = _externalQueue.pop();
#if 0
		std::cout << "Received externalEvent event " << _currEvent.name << std::endl;
#endif
		_currEvent.eventType = Event::EXTERNAL; // make sure it is set to external
		if (!_running)
			goto EXIT_INTERPRETER;

		USCXML_MONITOR_CALLBACK2(beforeProcessingEvent, _currEvent)

		if (_dataModel && iequals(_currEvent.name, "cancel.invoke." + _sessionId))
			break;

		if (_dataModel) {
			try {
				_dataModel.setEvent(_currEvent);
			} catch (Event e) {
				LOG(ERROR) << "Syntax error while setting external event:" << std::endl << e << std::endl << _currEvent;
			}
		}
		for (unsigned int i = 0; i < _configuration.size(); i++) {
			NodeSet<std::string> invokes = filterChildElements(_nsInfo.xmlNSPrefix + "invoke", _configuration[i]);
			for (unsigned int j = 0; j < invokes.size(); j++) {
				Element<std::string> invokeElem = (Element<std::string>)invokes[j];
				std::string invokeId;
				if (HAS_ATTR(invokeElem, "id")) {
					invokeId = ATTR(invokeElem, "id");
				} else {
					if (HAS_ATTR(invokeElem, "idlocation") && _dataModel) {
						try {
							invokeId = _dataModel.evalAsString(ATTR(invokeElem, "idlocation"));
						} catch(Event e) {
							LOG(ERROR) << "Syntax error while assigning idlocation from invoke:" << std::endl << e << std::endl;
						}
					}
				}
				std::string autoForward = invokeElem.getAttribute("autoforward");
				if (iequals(invokeId, _currEvent.invokeid)) {

					Arabica::XPath::NodeSet<std::string> finalizes = filterChildElements(_nsInfo.xmlNSPrefix + "finalize", invokeElem);
					for (int k = 0; k < finalizes.size(); k++) {
						Element<std::string> finalizeElem = Element<std::string>(finalizes[k]);
						executeContent(finalizeElem);
					}

				}
				if (iequals(autoForward, "true")) {
					try {
						// do not autoforward to invokers that send to #_parent from the SCXML IO Processor!
						// Yes do so, see test229!
						// if (!boost::equals(_currEvent.getOriginType(), "http://www.w3.org/TR/scxml/#SCXMLEventProcessor"))
						_invokers[invokeId].send(_currEvent);
					} catch(...) {
						LOG(ERROR) << "Exception caught while sending event to invoker " << invokeId;
					}
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
	USCXML_MONITOR_CALLBACK(beforeCompletion)

	exitInterpreter();
	if (_sendQueue) {
		std::map<std::string, std::pair<InterpreterImpl*, SendRequest> >::iterator sendIter = _sendIds.begin();
		while(sendIter != _sendIds.end()) {
			_sendQueue->cancelEvent(sendIter->first);
			sendIter++;
		}
	}

	USCXML_MONITOR_CALLBACK(afterCompletion)

}

/**
procedure exitInterpreter():
    statesToExit = configuration.toList().sort(exitOrder)
    for s in statesToExit:
        for content in s.onexit:
            executeContent(content)
        for inv in s.invoke:
            cancelInvoke(inv)
        configuration.delete(s)
        if isFinalState(s) and isScxmlState(s.parent):
            returnDoneEvent(s.donedata)
 */
void InterpreterRC::exitInterpreter() {
	NodeSet<std::string> statesToExit = _configuration;
	statesToExit.forward(false);
	statesToExit.sort();

	for (int i = 0; i < statesToExit.size(); i++) {
		Arabica::XPath::NodeSet<std::string> onExitElems = filterChildElements(_nsInfo.xmlNSPrefix + "onexit", statesToExit[i]);
		for (int j = 0; j < onExitElems.size(); j++) {
			executeContent(onExitElems[j]);
		}
		Arabica::XPath::NodeSet<std::string> invokeElems = filterChildElements(_nsInfo.xmlNSPrefix + "invoke", statesToExit[i]);
		for (int j = 0; j < invokeElems.size(); j++) {
			cancelInvoke(invokeElems[j]);
		}
		if (isFinal(statesToExit[i]) && parentIsScxmlState(statesToExit[i])) {
			returnDoneEvent(statesToExit[i]);
		}
	}
	_configuration = NodeSet<std::string>();
}

/**
function selectEventlessTransitions():
    enabledTransitions = new OrderedSet()
    atomicStates = configuration.toList().filter(isAtomicState).sort(documentOrder)
    for state in atomicStates:
        loop: for s in [state].append(getProperAncestors(state, null)):
            for t in s.transition:
                if not t.event and conditionMatch(t):
                    enabledTransitions.add(t)
                    break loop
    enabledTransitions = removeConflictingTransitions(enabledTransitions)
    return enabledTransitions
 */
Arabica::XPath::NodeSet<std::string> InterpreterRC::selectEventlessTransitions() {
	Arabica::XPath::NodeSet<std::string> enabledTransitions;

	NodeSet<std::string> atomicStates;
	for (unsigned int i = 0; i < _configuration.size(); i++) {
		if (isAtomic(_configuration[i]))
			atomicStates.push_back(_configuration[i]);
	}
	atomicStates.to_document_order();

	for (unsigned int i = 0; i < atomicStates.size(); i++) {
		const Node<std::string>& state = atomicStates[i];
		NodeSet<std::string> withAncestors;
		withAncestors.push_back(state);
		withAncestors.push_back(getProperAncestors(state, Node<std::string>()));
		for (unsigned int j = 0; j < withAncestors.size(); j++) {
			const Node<std::string>& ancestor = withAncestors[i];
			NodeSet<std::string> transitions = filterChildElements(_nsInfo.xmlNSPrefix + "transition", ancestor);
			for (unsigned int k = 0; k < transitions.size(); k++) {
				if (!HAS_ATTR(transitions[k], "event") && hasConditionMatch(transitions[k])) {
					enabledTransitions.push_back(transitions[k]);
					goto BREAK_LOOP;
				}
			}
		}
BREAK_LOOP:
		;
	}

	enabledTransitions = removeConflictingTransitions(enabledTransitions);
	return enabledTransitions;
}

/**
function selectTransitions(event):
    enabledTransitions = new OrderedSet()
    atomicStates = configuration.toList().filter(isAtomicState).sort(documentOrder)
    for state in atomicStates:
        loop: for s in [state].append(getProperAncestors(state, null)):
            for t in s.transition:
                if t.event and nameMatch(t.event, event.name) and conditionMatch(t):
                    enabledTransitions.add(t)
                    break loop
    enabledTransitions = removeConflictingTransitions(enabledTransitions)
    return enabledTransitions
 */
Arabica::XPath::NodeSet<std::string> InterpreterRC::selectTransitions(const std::string& event) {
	Arabica::XPath::NodeSet<std::string> enabledTransitions;

	NodeSet<std::string> atomicStates;
	for (unsigned int i = 0; i < _configuration.size(); i++) {
		if (isAtomic(_configuration[i]))
			atomicStates.push_back(_configuration[i]);
	}
	atomicStates.to_document_order();

#if 0
	std::cout << "selectTransitions for " << event << "========" << std::endl;
#endif
	for (unsigned int i = 0; i < atomicStates.size(); i++) {
		const Node<std::string>& state = atomicStates[i];
#if 0
		std::cout << "  == from " << ATTR(state, "id") << std::endl;
#endif

		NodeSet<std::string> withAncestors;
		withAncestors.push_back(state);
		withAncestors.push_back(getProperAncestors(state, Node<std::string>()));
		for (unsigned int j = 0; j < withAncestors.size(); j++) {
			const Node<std::string>& ancestor = withAncestors[j];
			NodeSet<std::string> transitions = filterChildElements(_nsInfo.xmlNSPrefix + "transition", ancestor);
			for (unsigned int k = 0; k < transitions.size(); k++) {
				if (isEnabledTransition(transitions[k], event)) {
					enabledTransitions.push_back(transitions[k]);
					goto BREAK_LOOP;
				}
			}
		}
BREAK_LOOP:
		;
	}

	enabledTransitions = removeConflictingTransitions(enabledTransitions);

#if 0
	std::cout << "enabledTransitions ========" << std::endl;
	for (unsigned int k = 0; k < enabledTransitions.size(); k++) {
		std::cout << enabledTransitions[k];
	}
	std::cout << std::endl;
	std::cout << "======== enabledTransitions" << std::endl;
#endif
	return enabledTransitions;
}

bool InterpreterRC::isEnabledTransition(const Node<std::string>& transition, const std::string& event) {
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


/**
function removeConflictingTransitions(enabledTransitions):
    filteredTransitions = new OrderedSet()
 // toList sorts the transitions in the order of the states that selected them
    for t1 in enabledTransitions.toList():
        t1Preempted = false;
        transitionsToRemove = new OrderedSet()
        for t2 in filteredTransitions.toList():
            if computeExitSet([t1]).hasIntersection(computeExitSet([t2])):
                if isDescendant(t1.source, t2.source):
                    transitionsToRemove.add(t2)
                else:
                    t1Preempted = true
                    break
        if not t1Preempted:
            for t3 in transitionsToRemove.toList():
                filteredTransitions.delete(t3)
            filteredTransitions.add(t1)

    return filteredTransitions
 */
Arabica::XPath::NodeSet<std::string> InterpreterRC::removeConflictingTransitions(const Arabica::XPath::NodeSet<std::string>& enabledTransitions) {
	Arabica::XPath::NodeSet<std::string> filteredTransitions;

	for (unsigned int i = 0; i < enabledTransitions.size(); i++) {
		const Node<std::string>& t1 = enabledTransitions[i];
		bool t1Preempted = false;
		Arabica::XPath::NodeSet<std::string> transitionsToRemove;

		for (unsigned int j = 0; j < filteredTransitions.size(); j++) {
			const Node<std::string>& t2 = enabledTransitions[j];
			if (hasIntersection(computeExitSet(t1), computeExitSet(t2))) {
				if (isDescendant(getSourceState(t1), getSourceState(t2))) {
					transitionsToRemove.push_back(t2);
				} else {
					t1Preempted = true;
					break;
				}
			}
		}

		if (!t1Preempted) {
			// remove transitionsToRemove from filteredTransitions
			std::list<Node<std::string> > tmp;
			for (int i = 0; i < filteredTransitions.size(); i++) {
				if (!isMember(filteredTransitions[i], transitionsToRemove)) {
					tmp.push_back(filteredTransitions[i]);
				}
			}
			filteredTransitions = NodeSet<std::string>();
			filteredTransitions.insert(_statesToInvoke.end(), tmp.begin(), tmp.end());

			filteredTransitions.push_back(t1);
		}
	}
	return filteredTransitions;
}

bool InterpreterRC::hasIntersection(const Arabica::XPath::NodeSet<std::string>& nodeSet1, const Arabica::XPath::NodeSet<std::string>& nodeSet2) {
	for (unsigned int i = 0; i < nodeSet1.size(); i++) {
		for (unsigned int j = 0; j < nodeSet2.size(); j++) {
			if (nodeSet1[i] == nodeSet2[j])
				return true;
		}
	}
	return false;
}

/**
procedure microstep(enabledTransitions):
    exitStates(enabledTransitions)
    executeTransitionContent(enabledTransitions)
    enterStates(enabledTransitions)
 */
void InterpreterRC::microstep(const Arabica::XPath::NodeSet<std::string>& enabledTransitions) {

	USCXML_MONITOR_CALLBACK(beforeMicroStep)

	exitStates(enabledTransitions);

	for (int i = 0; i < enabledTransitions.size(); i++) {
		Element<std::string> transition(enabledTransitions[i]);

		USCXML_MONITOR_CALLBACK3(beforeTakingTransition, transition, (i + 1 < enabledTransitions.size()))

		executeContent(transition);

		USCXML_MONITOR_CALLBACK3(afterTakingTransition, transition, (i + 1 < enabledTransitions.size()))
	}

	enterStates(enabledTransitions);

	USCXML_MONITOR_CALLBACK(afterMicroStep)
}


/**
procedure exitStates(enabledTransitions):
   statesToExit = computeExitSet(enabledTransitions)
   for s in statesToExit:
       statesToInvoke.delete(s)
   statesToExit = statesToExit.toList().sort(exitOrder)
   for s in statesToExit:
       for h in s.history:
           if h.type == "deep":
               f = lambda s0: isAtomicState(s0) and isDescendant(s0,s)
           else:
               f = lambda s0: s0.parent == s
            historyValue[h.id] = configuration.toList().filter(f)
   for s in statesToExit:
       for content in s.onexit:
           executeContent(content)
       for inv in s.invoke:
           cancelInvoke(inv)
       configuration.delete(s)
 */
void InterpreterRC::exitStates(const Arabica::XPath::NodeSet<std::string>& enabledTransitions) {
	NodeSet<std::string> statesToExit = computeExitSet(enabledTransitions);

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
		}
	}

	for (int i = 0; i < statesToExit.size(); i++) {
		USCXML_MONITOR_CALLBACK3(beforeExitingState, Element<std::string>(statesToExit[i]), (i + 1 < statesToExit.size()))

		NodeSet<std::string> onExits = filterChildElements(_nsInfo.xmlNSPrefix + "onExit", statesToExit[i]);
		for (int j = 0; j < onExits.size(); j++) {
			Element<std::string> onExitElem = (Element<std::string>)onExits[j];
			executeContent(onExitElem);
		}

		USCXML_MONITOR_CALLBACK3(afterExitingState, Element<std::string>(statesToExit[i]), (i + 1 < statesToExit.size()))

		NodeSet<std::string> invokes = filterChildElements(_nsInfo.xmlNSPrefix + "invoke", statesToExit[i]);
		for (int j = 0; j < invokes.size(); j++) {
			Element<std::string> invokeElem = (Element<std::string>)invokes[j];
			cancelInvoke(invokeElem);
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


/**
function computeExitSet(transitions)
	statesToExit = new OrderedSet
		for t in transitions:
			if(getTargetSet(t.target)):
				domain = getTransitionDomain(t)
				for s in configuration:
					if isDescendant(s,domain):
						statesToExit.add(s)
   return statesToExit
 */
Arabica::XPath::NodeSet<std::string> InterpreterRC::computeExitSet(const Arabica::XPath::NodeSet<std::string>& transitions) {
	NodeSet<std::string> statesToExit;
	for (unsigned int i = 0; i < transitions.size(); i++) {
		const Node<std::string>& t = transitions[i];
		if (isTargetless(t))
			continue;
		Arabica::DOM::Node<std::string> domain = getTransitionDomain(t);
		if (!domain)
			continue;
		for (unsigned int j = 0; j < _configuration.size(); j++) {
			const Node<std::string>& s = _configuration[j];
			if (isDescendant(s, domain)) {
				statesToExit.push_back(s);
			}
		}
	}
#if 0
	std::cout << "computeExitSet: ";
	for (int i = 0; i < statesToExit.size(); i++) {
		std::cout << ATTR(statesToExit[i], "id") << " ";
	}
	std::cout << std::endl;
#endif
	return statesToExit;
}

Arabica::XPath::NodeSet<std::string> InterpreterRC::computeExitSet(const Arabica::DOM::Node<std::string>& transition) {
	Arabica::XPath::NodeSet<std::string> transitions;
	transitions.push_back(transition);
	return computeExitSet(transitions);
}


/**
procedure enterStates(enabledTransitions):
    statesToEnter = new OrderedSet()
    statesForDefaultEntry = new OrderedSet()
    computeEntrySet(enabledTransitions, statesToEnter, statesForDefaultEntry)
    for s in statesToEnter.toList().sort(entryOrder):
        configuration.add(s)
        statesToInvoke.add(s)
        if binding == "late" and s.isFirstEntry:
            initializeDataModel(datamodel.s,doc.s)
            s.isFirstEntry = false
        for content in s.onentry:
            executeContent(content)
        if statesForDefaultEntry.isMember(s):
            executeContent(s.initial.transition)
        if isFinalState(s):
            if isSCXMLElement(s.parent):
                running = false
            else:
                parent = s.parent
                grandparent = parent.parent
                internalQueue.enqueue(new Event("done.state." + parent.id, s.donedata))
                if isParallelState(grandparent):
                    if getChildStates(grandparent).every(isInFinalState):
                        internalQueue.enqueue(new Event("done.state." + grandparent.id))
 */
void InterpreterRC::enterStates(const Arabica::XPath::NodeSet<std::string>& enabledTransitions) {
	NodeSet<std::string> statesToEnter;
	NodeSet<std::string> statesForDefaultEntry;
	// initialize the temporary table for default content in history states
	std::map<std::string, Arabica::DOM::Node<std::string> > defaultHistoryContent;

	computeEntrySet(enabledTransitions, statesToEnter, statesForDefaultEntry, defaultHistoryContent);
	statesToEnter.to_document_order();

	for (int i = 0; i < statesToEnter.size(); i++) {
		Element<std::string> s = (Element<std::string>)statesToEnter[i];

		USCXML_MONITOR_CALLBACK3(beforeEnteringState, s, i + 1 < statesToEnter.size())

		_configuration.push_back(s);
		_statesToInvoke.push_back(s);

		//		if (_binding == LATE && stateElem.getAttribute("isFirstEntry").size() > 0) {
		if (_binding == LATE && !isMember(s, _alreadyEntered)) {
			NodeSet<std::string> dataModelElems = filterChildElements(_nsInfo.xmlNSPrefix + "datamodel", s);
			if(dataModelElems.size() > 0 && _dataModel) {
				Arabica::XPath::NodeSet<std::string> dataElems = filterChildElements(_nsInfo.xmlNSPrefix + "data", dataModelElems[0]);
				for (int j = 0; j < dataElems.size(); j++) {
					if (dataElems[j].getNodeType() == Node_base::ELEMENT_NODE)
						initializeData(Element<std::string>(dataElems[j]));
				}
			}
			_alreadyEntered.push_back(s);
			//			stateElem.setAttribute("isFirstEntry", "");
		}
		// execute onentry executable content
		NodeSet<std::string> onEntryElems = filterChildElements(_nsInfo.xmlNSPrefix + "onEntry", s);
		executeContent(onEntryElems, false);

		USCXML_MONITOR_CALLBACK3(afterEnteringState, s, i + 1 < statesToEnter.size())

		if (isMember(s, statesForDefaultEntry)) {
			// execute initial transition content for compound states
			Arabica::XPath::NodeSet<std::string> transitions = _xpath.evaluate("" + _nsInfo.xpathPrefix + "initial/" + _nsInfo.xpathPrefix + "transition", s).asNodeSet();
			for (int j = 0; j < transitions.size(); j++) {
				executeContent(transitions[j]);
			}
		}
		if (defaultHistoryContent.find(ATTR(s, "id")) != defaultHistoryContent.end()) {
			executeContent(defaultHistoryContent[ATTR(s, "id")]);
		}

		/**
		if isFinalState(s):
		    if isSCXMLElement(s.parent):
		        running = false
		    else:
		        parent = s.parent
		        grandparent = parent.parent
		        internalQueue.enqueue(new Event("done.state." + parent.id, s.donedata))
		        if isParallelState(grandparent):
		            if getChildStates(grandparent).every(isInFinalState):
		                internalQueue.enqueue(new Event("done.state." + grandparent.id))
		*/
		//std::cout << _name << ": " << s << std::endl;

		if (isFinal(s)) {
			internalDoneSend(s);
			if (parentIsScxmlState(s)) {
				_running = false;
				_topLevelFinalReached = true;
			} else {
				Element<std::string> parent = (Element<std::string>)s.getParentNode();
				Element<std::string> grandParent = (Element<std::string>)parent.getParentNode();

				internalDoneSend(parent);

				if (isParallel(grandParent)) {
					Arabica::XPath::NodeSet<std::string> childs = getChildStates(grandParent);
					bool inFinalState = true;
					for (int j = 0; j < childs.size(); j++) {
						if (!isInFinalState(childs[j])) {
							inFinalState = false;
							break;
						}
					}
					if (inFinalState) {
						internalDoneSend(grandParent);
					}
				}
			}
		}
	}
}


/**
procedure computeEntrySet(transitions, statesToEnter, statesForDefaultEntry)
   for t in transitions:
        statesToEnter.union(getTargetStates(t.target))
    for s in statesToEnter:
        addDescendantStatesToEnter(s,statesToEnter,statesForDefaultEntry)
    for t in transitions:
        ancestor = getTransitionDomain(t)
        for s in getTargetStates(t.target)):
            addAncestorStatesToEnter(s, ancestor, statesToEnter, statesForDefaultEntry)
 */
void InterpreterRC::computeEntrySet(const Arabica::XPath::NodeSet<std::string>& transitions,
                                    NodeSet<std::string>& statesToEnter,
                                    NodeSet<std::string>& statesForDefaultEntry,
                                    std::map<std::string, Arabica::DOM::Node<std::string> > defaultHistoryContent) {
	for (int i = 0; i < transitions.size(); i++) {
		const Node<std::string>& t = transitions[i];

		NodeSet<std::string> targets = getTargetStates(t);
		for (int j = 0; j < targets.size(); j++) {
			if (!isMember(targets[j], statesToEnter)) {
				statesToEnter.push_back(targets[j]);
			}
		}
	}

#if 0
	std::cout << "before addDescendantStatesToEnter: ";
	for (int i = 0; i < statesToEnter.size(); i++) {
		std::cout << ATTR(statesToEnter[i], "id") << " ";
	}
	std::cout << std::endl;
#endif

	NodeSet<std::string> tmp = statesToEnter;
	for (int i = 0; i < tmp.size(); i++) {
		assert(tmp[i]);
		addDescendantStatesToEnter(tmp[i],statesToEnter,statesForDefaultEntry, defaultHistoryContent);
	}

#if 0
	std::cout << "after addDescendantStatesToEnter: ";
	for (int i = 0; i < statesToEnter.size(); i++) {
		std::cout << ATTR(statesToEnter[i], "id") << " ";
	}
	std::cout << std::endl;
#endif

	for (int i = 0; i < transitions.size(); i++) {
		Element<std::string> t = (Element<std::string>)transitions[i];
		Node<std::string> ancestor = getTransitionDomain(t);
		NodeSet<std::string> targets = getTargetStates(t);
		for (int j = 0; j < targets.size(); j++) {
			const Node<std::string>& s = targets[j];
			addAncestorStatesToEnter(s, ancestor, statesToEnter, statesForDefaultEntry, defaultHistoryContent);
		}
	}

#if 0
	std::cout << "after addAncestorStatesToEnter: ";
	for (int i = 0; i < statesToEnter.size(); i++) {
		std::cout << ATTR(statesToEnter[i], "id") << " ";
	}
	std::cout << std::endl;
#endif
}

void InterpreterRC::computeEntrySet(const Arabica::DOM::Node<std::string>& transition,
                                    NodeSet<std::string>& statesToEnter,
                                    NodeSet<std::string>& statesForDefaultEntry,
                                    std::map<std::string, Arabica::DOM::Node<std::string> > defaultHistoryContent) {
	Arabica::XPath::NodeSet<std::string> transitions;
	transitions.push_back(transition);
	computeEntrySet(transitions, statesToEnter, statesForDefaultEntry, defaultHistoryContent);
}


/**
procedure addDescendantStatesToEnter(state,statesToEnter,statesForDefaultEntry):
    if isHistoryState(state):
        if historyValue[state.id]:
            for s in historyValue[state.id]:
                addDescendantStatesToEnter(s,statesToEnter,statesForDefaultEntry)
                addAncestorStatesToEnter(s, state.parent, statesToEnter, statesForDefaultEntry)
        else:
            for t in state.transition:
                for s in getTargetStates(t.target):
                    addDescendantStatesToEnter(s,statesToEnter,statesForDefaultEntry)
                    addAncestorStatesToEnter(s, state.parent, statesToEnter, statesForDefaultEntry)
    else:
        statesToEnter.add(state)
        if isCompoundState(state):
            statesForDefaultEntry.add(state)
            for s in getTargetStates(state.initial):
                addDescendantStatesToEnter(s,statesToEnter,statesForDefaultEntry)
                addAncestorStatesToEnter(s, state, statesToEnter, statesForDefaultEntry)
        else:
            if isParallelState(state):
                for child in getChildStates(state):
                    if not statesToEnter.some(lambda s: isDescendant(s,child)):
                        addDescendantStatesToEnter(child,statesToEnter,statesForDefaultEntry)
 */
void InterpreterRC::addDescendantStatesToEnter(const Arabica::DOM::Node<std::string>& state,
        Arabica::XPath::NodeSet<std::string>& statesToEnter,
        Arabica::XPath::NodeSet<std::string>& statesForDefaultEntry,
        std::map<std::string, Arabica::DOM::Node<std::string> > defaultHistoryContent) {
	if (isHistory(state)) {
		std::string stateId = ATTR(state, "id");
		if (_historyValue.find(stateId) != _historyValue.end()) {
			const Arabica::XPath::NodeSet<std::string>& historyValue = _historyValue[stateId];
			for (int i = 0; i < historyValue.size(); i++) {
				const Node<std::string>& s = historyValue[i];
				addDescendantStatesToEnter(s,statesToEnter,statesForDefaultEntry, defaultHistoryContent);
				addAncestorStatesToEnter(s, getParentState(s), statesToEnter, statesForDefaultEntry, defaultHistoryContent);
			}
		} else {
			NodeSet<std::string> transitions = filterChildElements(_nsInfo.xmlNSPrefix + "transition", state);
			if (transitions.size() > 0) {
				defaultHistoryContent[ATTR(state, "id")] = transitions[0];
			}
			if (transitions.size() > 1) {
				LOG(ERROR) << "Only one transition allowed in history";
			}
			for (int i = 0; i < transitions.size(); i++) {
				NodeSet<std::string> targets = getTargetStates(transitions[i]);
				for (int j = 0; j < targets.size(); j++) {
					const Node<std::string>& s = targets[i];
					addDescendantStatesToEnter(s,statesToEnter,statesForDefaultEntry, defaultHistoryContent);
					addAncestorStatesToEnter(s, getParentState(s), statesToEnter, statesForDefaultEntry, defaultHistoryContent);
				}
			}
		}
	} else {
		if (!isMember(state, statesToEnter)) // adding an existing element invalidates old reference
			statesToEnter.push_back(state);

		if (isCompound(state)) {
			statesForDefaultEntry.push_back(state);
			NodeSet<std::string> targets = getInitialStates(state);
			for (int i = 0; i < targets.size(); i++) {
				const Node<std::string>& s = targets[i];
				addDescendantStatesToEnter(s,statesToEnter,statesForDefaultEntry, defaultHistoryContent);
				addAncestorStatesToEnter(s, getParentState(s), statesToEnter, statesForDefaultEntry, defaultHistoryContent);
			}
		} else if(isParallel(state)) {
			// if state is a parallel state, recursively call addStatesToEnter on any of its child
			// states that don't already have a descendant on statesToEnter.
			NodeSet<std::string> childStates = getChildStates(state);
			for (int i = 0; i < childStates.size(); i++) {
				const Node<std::string>& child = childStates[i];
				for (int j = 0; j < statesToEnter.size(); j++) {
					const Node<std::string>& s = statesToEnter[j];
					if (isDescendant(s, child)) {
						goto BREAK_LOOP;
					}
				}
				addDescendantStatesToEnter(child,statesToEnter,statesForDefaultEntry, defaultHistoryContent);
BREAK_LOOP:
				;
			}
		}
	}
}


/**
procedure addAncestorStatesToEnter(state, ancestor, statesToEnter, statesForDefaultEntry)
   for anc in getProperAncestors(state,ancestor):
       statesToEnter.add(anc)
       if isParallelState(anc):
           for child in getChildStates(anc):
               if not statesToEnter.some(lambda s: isDescendant(s,child)):
                   addDescendantStatesToEnter(child,statesToEnter,statesForDefaultEntry)
 */
void InterpreterRC::addAncestorStatesToEnter(const Arabica::DOM::Node<std::string>& state,
        const Arabica::DOM::Node<std::string>& ancestor,
        Arabica::XPath::NodeSet<std::string>& statesToEnter,
        Arabica::XPath::NodeSet<std::string>& statesForDefaultEntry,
        std::map<std::string, Arabica::DOM::Node<std::string> > defaultHistoryContent) {
	NodeSet<std::string> ancestors = getProperAncestors(state,ancestor);
	for (int i = 0; i < ancestors.size(); i++) {
		const Node<std::string>& anc = ancestors[i];
		statesToEnter.push_back(anc);
		if (isParallel(anc)) {
			NodeSet<std::string> childStates = getChildStates(anc);
			for (int j = 0; j < childStates.size(); j++) {
				const Node<std::string>& child = childStates[j];
				for (int k = 0; k < statesToEnter.size(); k++) {
					const Node<std::string>& s = statesToEnter[k];
					if (isDescendant(s, child)) {
						goto BREAK_LOOP;
					}
				}
				addDescendantStatesToEnter(child,statesToEnter,statesForDefaultEntry, defaultHistoryContent);
BREAK_LOOP:
				;
			}
		}
	}
}

/**
function isInFinalState(s):
    if isCompoundState(s):
        return getChildStates(s).some(lambda s: isFinalState(s) and configuration.isMember(s))
    elif isParallelState(s):
        return getChildStates(s).every(isInFinalState)
    else:
        return false
*/
bool InterpreterRC::isInFinalState(const Arabica::DOM::Node<std::string>& state) {
	if (isCompound(state)) {
		Arabica::XPath::NodeSet<std::string> childs = getChildStates(state);
		for (int i = 0; i < childs.size(); i++) {
			if (isFinal(childs[i]) && isMember(childs[i], _configuration))
				return true;
		}
	} else if (isParallel(state)) {
		Arabica::XPath::NodeSet<std::string> childs = getChildStates(state);
		for (int i = 0; i < childs.size(); i++) {
			if (!isInFinalState(childs[i]))
				return false;
		}
		return true;
	}
	return false;
}


/**
function getTransitionDomain(t)
  tstates = getTargetStates(t.target)
  if not tstates
      return t.source
    elif t.type == "internal" and isCompoundState(t.source) and tstates.every(lambda s: isDescendant(s,t.source)):
      return t.source
  else:
      return findLCCA([t.source].append(tstates))
 */
Arabica::DOM::Node<std::string> InterpreterRC::getTransitionDomain(const Arabica::DOM::Node<std::string>& transition) {
	NodeSet<std::string> tStates = getTargetStates(transition);
	Node<std::string> source = getSourceState(transition);

#if 0
	std::cout << "getTransitionDomain: " << std::endl << transition << std::endl;
#endif

	if (tStates.size() == 0) {
		return Arabica::DOM::Node<std::string>(); // null
	}
	std::string transitionType = (HAS_ATTR(transition, "type") ? ATTR(transition, "type") : "external");

	if (iequals(transitionType, "internal") && isCompound(source)) {
		for (int i = 0; i < tStates.size(); i++) {
			const Node<std::string>& s = tStates[i];
			if (!isDescendant(s, source))
				goto BREAK_LOOP;
		}
		return source;
	}
BREAK_LOOP:
	;
	Arabica::XPath::NodeSet<std::string> states;
	states.push_back(source);
	states.push_back(tStates);
	return findLCCA(states);
}


/**
function findLCCA(stateList):
    for anc in getProperAncestors(stateList.head(),null).filter(isCompoundStateOrScxmlElement):
        if stateList.tail().every(lambda s: isDescendant(s,anc)):
            return anc
 */
Arabica::DOM::Node<std::string> InterpreterRC::findLCCA(const Arabica::XPath::NodeSet<std::string>& states) {
	Arabica::XPath::NodeSet<std::string> ancestors = getProperAncestors(states[0], Arabica::DOM::Node<std::string>());
	//	ancestors.push_back(states[0]); // state[0] may already be the ancestor - bug in W3C spec?
	Arabica::DOM::Node<std::string> ancestor;
	for (int i = 0; i < ancestors.size(); i++) {
		if (!isCompound(ancestors[i]))
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

	// take uppermost root as ancestor
	if (!ancestor)
		ancestor = _scxml;
	assert(ancestor);
	return ancestor;
}

/**
 If state2 is null, returns the set of all ancestors of state1 in ancestry order
 (state1's parent followed by the parent's parent, etc. up to an including the
 <scxml> element). If state2 is non-null, returns inancestry order the set of all
 ancestors of state1, up to but not including state2. (A "proper ancestor" of a
 state is its parent, or the parent's parent, or the parent's parent's parent,
 etc.)) If state2 is state1's parent, or equal to state1, or a descendant of
 state1, this returns the empty set.
*/
Arabica::XPath::NodeSet<std::string> InterpreterRC::getProperAncestors(const Arabica::DOM::Node<std::string>& state1, const Arabica::DOM::Node<std::string>& state2) {
	NodeSet<std::string> ancestors;

	if (!state1 || !isState(state1))
		return ancestors;

	if (!state2) {
		/**
		 If state2 is null, returns the set of all ancestors of state1 in ancestry
		 order (state1's parent followed by the parent's parent, etc. up to an
		 including the <scxml> element).
		 */
		Arabica::DOM::Node<std::string> parent = state1.getParentNode();
		while(parent && isState(parent)) {
			ancestors.push_back(parent);
			parent = parent.getParentNode();
		}
		return ancestors;
	}

	/**
	 If state2 is state1's parent, or equal to state1, or a descendant of
	 state1, this returns the empty set
	*/
	if (state1.getParentNode() == state2 || state1 == state2 || isDescendant(state2, state1)) {
		return ancestors;
	}

	/**
	 If state2 is non-null, returns in ancestry order the set of all ancestors
	 of state1, up to but not including state2.
	 */
	Arabica::DOM::Node<std::string> parent = state1.getParentNode();
	while(parent && isState(parent) && parent != state2) {
		ancestors.push_back(parent);
		parent = parent.getParentNode();
	}
	return ancestors;
}

NodeSet<std::string> InterpreterRC::getTargetStates(const Arabica::DOM::Node<std::string>& transition) {
	NodeSet<std::string> targetStates;

	std::string targetId = ((Arabica::DOM::Element<std::string>)transition).getAttribute("target");
	std::list<std::string> targetIds = InterpreterImpl::tokenizeIdRefs(ATTR(transition, "target"));
	if (targetIds.size() > 0) {
		for (std::list<std::string>::const_iterator targetIter = targetIds.begin(); targetIter != targetIds.end(); targetIter++) {
			Arabica::DOM::Node<std::string> state = getState(*targetIter);
			if (state) {
				assert(HAS_ATTR(state, "id"));
				targetStates.push_back(state);
			}
		}
	} else {
		targetStates.push_back(getSourceState(transition)); // TODO: is this till correct?
	}
	return targetStates;
}


#if 0
/**
Returns 'true' if state1 is a descendant of state2 (a child, or a child of a child, or a child of a child of a child, etc.) Otherwise returns 'false'.
*/
bool InterpreterRC::isDescendant(const Arabica::DOM::Node<std::string>& state1, const Arabica::DOM::Node<std::string>& state2) {
	return false;
}

/**
Returns a list containing all <state>, <final>, and <parallel> children of state1.
*/
Arabica::XPath::NodeSet<std::string> InterpreterRC::getChildStates(const Arabica::DOM::Node<std::string>& state) {
	return Arabica::XPath::NodeSet<std::string>();
}
#endif


}