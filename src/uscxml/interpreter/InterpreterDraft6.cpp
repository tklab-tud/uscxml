#include "InterpreterDraft6.h"

#include <glog/logging.h>

namespace uscxml {

using namespace Arabica::XPath;
using namespace Arabica::DOM;

// see: http://www.w3.org/TR/scxml/#AlgorithmforSCXMLInterpretation
void InterpreterDraft6::interpret() {
//	_mutex.lock();
	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
	if (!_isInitialized)
		init();

//	std::cout << _scxml << std::endl;

	if (!_scxml) {
//		_mutex.unlock();
		return;
	}
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
	} else {
		_dataModel = _factory->createDataModel("null", this);
	}
	if(datamodelName.length() > 0  && !_dataModel) {
		LOG(ERROR) << "No datamodel for " << datamodelName << " registered";
	}

	if (_dataModel) {
		_dataModel.assign("_x.args", _cmdLineOptions);
	}

	_running = true;
	_binding = (HAS_ATTR(_scxml, "binding") && boost::iequals(ATTR(_scxml, "binding"), "late") ? LATE : EARLY);

	// @TODO: Reread http://www.w3.org/TR/scxml/#DataBinding

	if (_dataModel && _binding == EARLY) {
		// initialize all data elements
		NodeSet<std::string> dataElems = _xpath.evaluate("//" + _xpathPrefix + "data", _scxml).asNodeSet();
		for (unsigned int i = 0; i < dataElems.size(); i++) {
			// do not process data elements of nested documents from invokers
			if (!getAncestorElement(dataElems[i], _xmlNSPrefix + "invoke"))
				if (dataElems[i].getNodeType() == Node_base::ELEMENT_NODE)
					initializeData(Element<std::string>(dataElems[i]));
		}
	} else if(_dataModel) {
		// initialize current data elements
		NodeSet<std::string> topDataElems = filterChildElements(_xmlNSPrefix + "data", filterChildElements(_xmlNSPrefix + "datamodel", _scxml));
		for (unsigned int i = 0; i < topDataElems.size(); i++) {
			if (topDataElems[i].getNodeType() == Node_base::ELEMENT_NODE)
				initializeData(Element<std::string>(topDataElems[i]));
		}
	}

	// executeGlobalScriptElements
	NodeSet<std::string> globalScriptElems = filterChildElements(_xmlNSPrefix + "script", _scxml);
	for (unsigned int i = 0; i < globalScriptElems.size(); i++) {
		if (_dataModel) {
			executeContent(globalScriptElems[i]);
		}
	}

	NodeSet<std::string> initialTransitions;

	if (_userDefinedStartConfiguration.size() > 0) {
		// we emulate entering a given configuration by creating a pseudo deep history
		Element<std::string> initHistory = _document.createElementNS(_nsURL, "history");
		initHistory.setAttribute("id", getUUID());
		initHistory.setAttribute("type", "deep");
		_scxml.insertBefore(initHistory, _scxml.getFirstChild());

		std::string histId = ATTR(initHistory, "id");
		NodeSet<std::string> histStates;
		for (int i = 0; i < _userDefinedStartConfiguration.size(); i++) {
			histStates.push_back(getState(_userDefinedStartConfiguration[i]));
		}
		_historyValue[histId] = histStates;

		Element<std::string> initialElem = _document.createElementNS(_nsURL, "initial");
		initialElem.setAttribute("generated", "true");
		Element<std::string> transitionElem = _document.createElementNS(_nsURL, "transition");
		transitionElem.setAttribute("target", histId);
		initialElem.appendChild(transitionElem);
		_scxml.appendChild(initialElem);
		initialTransitions.push_back(transitionElem);

	} else {
		// try to get initial transition form initial element
		initialTransitions = _xpath.evaluate("/" + _xpathPrefix + "initial/" + _xpathPrefix + "transition", _scxml).asNodeSet();
		if (initialTransitions.size() == 0) {
			Arabica::XPath::NodeSet<std::string> initialStates;
			// fetch per draft
			initialStates = getInitialStates();
			assert(initialStates.size() > 0);
			for (int i = 0; i < initialStates.size(); i++) {
				Element<std::string> initialElem = _document.createElementNS(_nsURL, "initial");
				initialElem.setAttribute("generated", "true");
				Element<std::string> transitionElem = _document.createElementNS(_nsURL, "transition");
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

	// set datamodel to null from this thread
	if(_dataModel)
		_dataModel = DataModel();

}


void InterpreterDraft6::mainEventLoop() {
	std::set<InterpreterMonitor*>::iterator monIter;

	while(_running) {
		NodeSet<std::string> enabledTransitions;
		_stable = false;

		// Here we handle eventless transitions and transitions
		// triggered by internal events until machine is stable
		while(_running && !_stable) {
#if 0
			std::cout << "Configuration: ";
			for (int i = 0; i < _configuration.size(); i++) {
				std::cout << ATTR(_configuration[i], "id") << ", ";
			}
			std::cout << std::endl;
#endif
			monIter = _monitors.begin();
			while(monIter != _monitors.end()) {
				try {
					(*monIter)->beforeMicroStep(shared_from_this());
				} catch (Event e) {
					LOG(ERROR) << "Syntax error when calling beforeMicroStep on monitors: " << std::endl << e << std::endl;
				} catch (boost::bad_weak_ptr e) {
					LOG(ERROR) << "Unclean shutdown " << std::endl << std::endl;
					_mutex.unlock();
					goto EXIT_INTERPRETER;
				} catch (...) {
					LOG(ERROR) << "An exception occured when calling beforeMicroStep on monitors";
				}
				monIter++;
			}

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
					if (_dataModel)
						_dataModel.setEvent(_currEvent);
					enabledTransitions = selectTransitions(_currEvent.name);
				}
			}
			if (!enabledTransitions.empty()) {
				monIter = _monitors.begin();
				while(monIter != _monitors.end()) {
					try {
						(*monIter)->beforeTakingTransitions(shared_from_this(), enabledTransitions);
					} catch (Event e) {
						LOG(ERROR) << "Syntax error when calling beforeTakingTransitions on monitors: " << std::endl << e << std::endl;
					} catch (boost::bad_weak_ptr e) {
						LOG(ERROR) << "Unclean shutdown " << std::endl << std::endl;
						_mutex.unlock();
						goto EXIT_INTERPRETER;
					} catch (...) {
						LOG(ERROR) << "An exception occured when calling beforeTakingTransitions on monitors";
					}
					monIter++;
				}
				// test 403b
				enabledTransitions.to_document_order();
				microstep(enabledTransitions);
			}
		}

		for (unsigned int i = 0; i < _statesToInvoke.size(); i++) {
			NodeSet<std::string> invokes = filterChildElements(_xmlNSPrefix + "invoke", _statesToInvoke[i]);
			for (unsigned int j = 0; j < invokes.size(); j++) {
				invoke(invokes[j]);
			}
		}

		_statesToInvoke = NodeSet<std::string>();
		if (!_internalQueue.empty())
			continue;

		// assume that we have a legal configuration as soon as the internal queue is empty
		assert(hasLegalConfiguration());

		monIter = _monitors.begin();
//    if (!_sendQueue || _sendQueue->isEmpty()) {
		while(monIter != _monitors.end()) {
			try {
				(*monIter)->onStableConfiguration(shared_from_this());
			} catch (Event e) {
				LOG(ERROR) << "Syntax error when calling onStableConfiguration on monitors: " << std::endl << e << std::endl;
			} catch (boost::bad_weak_ptr e) {
				LOG(ERROR) << "Unclean shutdown " << std::endl << std::endl;
				_mutex.unlock();
				goto EXIT_INTERPRETER;
			} catch (...) {
				LOG(ERROR) << "An exception occured when calling onStableConfiguration on monitors";
			}
			monIter++;
		}
//    }

		_mutex.unlock();
		// whenever we have a stable configuration, run the mainThread hooks with 200fps
		while(_externalQueue.isEmpty() && _thread == NULL) {
			runOnMainThread(200);
		}

		_currEvent = _externalQueue.pop();
#if VERBOSE
		std::cout << "Received externalEvent event " << _currEvent.name << std::endl;
#endif
		_currEvent.eventType = Event::EXTERNAL; // make sure it is set to external
		if (!_running)
			goto EXIT_INTERPRETER;

		_mutex.lock();

		if (_dataModel && boost::iequals(_currEvent.name, "cancel.invoke." + _sessionId))
			break;

		if (_dataModel) {
			try {
				_dataModel.setEvent(_currEvent);
			} catch (Event e) {
				LOG(ERROR) << "Syntax error while setting external event:" << std::endl << e << std::endl;
			}
		}
		for (unsigned int i = 0; i < _configuration.size(); i++) {
			NodeSet<std::string> invokes = filterChildElements(_xmlNSPrefix + "invoke", _configuration[i]);
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
				if (boost::iequals(invokeId, _currEvent.invokeid)) {

					Arabica::XPath::NodeSet<std::string> finalizes = filterChildElements(_xmlNSPrefix + "finalize", invokeElem);
					for (int k = 0; k < finalizes.size(); k++) {
						Element<std::string> finalizeElem = Element<std::string>(finalizes[k]);
						executeContent(finalizeElem);
					}

				}
				if (boost::iequals(autoForward, "true")) {
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
	monIter = _monitors.begin();
	while(monIter != _monitors.end()) {
		try {
			(*monIter)->beforeCompletion(shared_from_this());
		} catch (Event e) {
			LOG(ERROR) << "Syntax error when calling beforeCompletion on monitors: " << std::endl << e << std::endl;
		} catch (boost::bad_weak_ptr e) {
			LOG(ERROR) << "Unclean shutdown " << std::endl << std::endl;
			exitInterpreter();
		} catch (...) {
			LOG(ERROR) << "An exception occured when calling beforeCompletion on monitors";
		}
		monIter++;
	}

	exitInterpreter();
	if (_sendQueue) {
		std::map<std::string, std::pair<InterpreterImpl*, SendRequest> >::iterator sendIter = _sendIds.begin();
		while(sendIter != _sendIds.end()) {
			_sendQueue->cancelEvent(sendIter->first);
			sendIter++;
		}
	}

	monIter = _monitors.begin();
	while(monIter != _monitors.end()) {
		try {
			(*monIter)->afterCompletion(shared_from_this());
		} catch (Event e) {
			LOG(ERROR) << "Syntax error when calling afterCompletion on monitors: " << std::endl << e << std::endl;
		} catch (boost::bad_weak_ptr e) {
			LOG(ERROR) << "Unclean shutdown " << std::endl << std::endl;
			exitInterpreter();
		} catch (...) {
			LOG(ERROR) << "An exception occured when calling afterCompletion on monitors";
		}
		monIter++;
	}

}

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
		NodeSet<std::string> transitions = filterChildElements(_xmlNSPrefix + "transition", states[index]);
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

#if 0
	std::cout << "Enabled transitions: " << std::endl;
	for (int i = 0; i < enabledTransitions.size(); i++) {
		std::cout << enabledTransitions[i] << std::endl << "----" << std::endl;
	}
	std::cout << std::endl;
#endif

	enabledTransitions = filterPreempted(enabledTransitions);
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

	std::vector<std::string> eventNames = tokenizeIdRefs(eventName);

	std::vector<std::string>::iterator eventIter = eventNames.begin();
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
		NodeSet<std::string> transitions = filterChildElements(_xmlNSPrefix + "transition", states[index]);
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
	if (HAS_ATTR(transition, "type") && boost::iequals(ATTR(transition, "type"), "internal")) {
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
#if 0
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

	exitStates(enabledTransitions);
	executeContent(enabledTransitions);
	enterStates(enabledTransitions);
}

void InterpreterDraft6::exitInterpreter() {
	NodeSet<std::string> statesToExit = _configuration;
	statesToExit.forward(false);
	statesToExit.sort();

	for (int i = 0; i < statesToExit.size(); i++) {
		Arabica::XPath::NodeSet<std::string> onExitElems = filterChildElements(_xmlNSPrefix + "onexit", statesToExit[i]);
		for (int j = 0; j < onExitElems.size(); j++) {
			executeContent(onExitElems[j]);
		}
		Arabica::XPath::NodeSet<std::string> invokeElems = filterChildElements(_xmlNSPrefix + "invoke", statesToExit[i]);
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
	std::set<InterpreterMonitor*>::iterator monIter;

#if VERBOSE
	std::cout << "Enabled exit transitions: " << std::endl;
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
			bool isInternal = (HAS_ATTR(t, "type") && boost::iequals(ATTR(t, "type"), "internal")); // external is default
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
				std::cout << "tmpStates: ";
				for (int i = 0; i < tmpStates.size(); i++) {
					std::cout << ATTR(tmpStates[i], "id") << ", ";
				}
				std::cout << std::endl;
#endif
				ancestor = findLCCA(tmpStates);
			}
#if VERBOSE
			std::cout << "Ancestor: " << ATTR(ancestor, "id") << std::endl;;
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
	std::cout << "States to exit: ";
	for (int i = 0; i < statesToExit.size(); i++) {
		std::cout << LOCALNAME(statesToExit[i]) << ":" << ATTR(statesToExit[i], "id") << ", ";
	}
	std::cout << std::endl;
#endif

	monIter = _monitors.begin();
	while(monIter != _monitors.end()) {
		try {
			(*monIter)->beforeExitingStates(shared_from_this(), statesToExit);
		} catch (Event e) {
			LOG(ERROR) << "Syntax error when calling beforeExitingStates on monitors: " << std::endl << e << std::endl;
		} catch (boost::bad_weak_ptr e) {
			LOG(ERROR) << "Unclean shutdown " << std::endl << std::endl;
			exitInterpreter();
		} catch (...) {
			LOG(ERROR) << "An exception occured when calling beforeExitingStates on monitors";
		}
		monIter++;
	}

	for (int i = 0; i < statesToExit.size(); i++) {
		NodeSet<std::string> histories = filterChildElements(_xmlNSPrefix + "history", statesToExit[i]);
		for (int j = 0; j < histories.size(); j++) {
			Element<std::string> historyElem = (Element<std::string>)histories[j];
			std::string historyType = (historyElem.hasAttribute("type") ? historyElem.getAttribute("type") : "shallow");
			NodeSet<std::string> historyNodes;
			for (int k = 0; k < _configuration.size(); k++) {
				if (boost::iequals(historyType, "deep")) {
					if (isAtomic(_configuration[k]) && isDescendant(_configuration[k], statesToExit[i]))
						historyNodes.push_back(_configuration[k]);
				} else {
					if (_configuration[k].getParentNode() == statesToExit[i])
						historyNodes.push_back(_configuration[k]);
				}
			}
			_historyValue[historyElem.getAttribute("id")] = historyNodes;
#if 0
			std::cout << "History node " << ATTR(historyElem, "id") << " contains: ";
			for (int i = 0; i < historyNodes.size(); i++) {
				std::cout << ATTR(historyNodes[i], "id") << ", ";
			}
			std::cout << std::endl;
#endif

		}
	}

	for (int i = 0; i < statesToExit.size(); i++) {
		NodeSet<std::string> onExits = filterChildElements(_xmlNSPrefix + "onExit", statesToExit[i]);
		for (int j = 0; j < onExits.size(); j++) {
			Element<std::string> onExitElem = (Element<std::string>)onExits[j];
			executeContent(onExitElem);
		}
		NodeSet<std::string> invokes = filterChildElements(_xmlNSPrefix + "invoke", statesToExit[i]);
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

	monIter = _monitors.begin();
	while(monIter != _monitors.end()) {
		try {
			(*monIter)->afterExitingStates(shared_from_this());
		} catch (Event e) {
			LOG(ERROR) << "Syntax error when calling afterExitingStates on monitors: " << std::endl << e << std::endl;
		} catch (boost::bad_weak_ptr e) {
			LOG(ERROR) << "Unclean shutdown " << std::endl << std::endl;
			exitInterpreter();
		} catch (...) {
			LOG(ERROR) << "An exception occured when calling afterExitingStates on monitors";
		}
		monIter++;
	}

}

void InterpreterDraft6::enterStates(const Arabica::XPath::NodeSet<std::string>& enabledTransitions) {
	NodeSet<std::string> statesToEnter;
	NodeSet<std::string> statesForDefaultEntry;
	std::set<InterpreterMonitor*>::iterator monIter;

#if VERBOSE
	std::cout << "Enabled enter transitions: " << std::endl;
	for (int i = 0; i < enabledTransitions.size(); i++) {
		std::cout << enabledTransitions[i] << std::endl;
	}
	std::cout << std::endl;
#endif

	for (int i = 0; i < enabledTransitions.size(); i++) {
		Element<std::string> transition = ((Element<std::string>)enabledTransitions[i]);
		if (!isTargetless(transition)) {
			std::string transitionType = (boost::iequals(transition.getAttribute("type"), "internal") ? "internal" : "external");
			NodeSet<std::string> tStates = getTargetStates(transition);

#if VERBOSE
			std::cout << "Target States: ";
			for (int i = 0; i < tStates.size(); i++) {
				std::cout << ATTR(tStates[i], "id") << ", ";
			}
			std::cout << std::endl;
#endif

			Node<std::string> ancestor;
			Node<std::string> source = getSourceState(transition);
#if VERBOSE
			std::cout << "Source States: " << ATTR(source, "id") << std::endl;
#endif
			assert(source);

			bool allDescendants = true;
			for (int j = 0; j < tStates.size(); j++) {
				if (!isDescendant(tStates[j], source)) {
					allDescendants = false;
					break;
				}
			}
			if (boost::iequals(transitionType, "internal") &&
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
			std::cout << "Ancestor: " << ATTR(ancestor, "id") << std::endl;
#endif

			for (int j = 0; j < tStates.size(); j++) {
				addStatesToEnter(tStates[j], statesToEnter, statesForDefaultEntry);
			}

#if VERBOSE
			std::cout << "States to enter: ";
			for (int i = 0; i < statesToEnter.size(); i++) {
				std::cout << LOCALNAME(statesToEnter[i]) << ":" << ATTR(statesToEnter[i], "id") << ", ";
			}
			std::cout << std::endl;
#endif

			for (int j = 0; j < tStates.size(); j++) {
				NodeSet<std::string> ancestors = getProperAncestors(tStates[j], ancestor);

#if VERBOSE
				std::cout << "Proper Ancestors of " << ATTR(tStates[j], "id") << " and " << ATTR(ancestor, "id") << ": ";
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
	std::cout << "States to enter: ";
	for (int i = 0; i < statesToEnter.size(); i++) {
		std::cout << ATTR(statesToEnter[i], "id") << ", ";
	}
	std::cout << std::endl;
#endif

	monIter = _monitors.begin();
	while(monIter != _monitors.end()) {
		try {
			(*monIter)->beforeEnteringStates(shared_from_this(), statesToEnter);
		} catch (Event e) {
			LOG(ERROR) << "Syntax error when calling beforeEnteringStates on monitors: " << std::endl << e << std::endl;
		} catch (boost::bad_weak_ptr e) {
			LOG(ERROR) << "Unclean shutdown " << std::endl << std::endl;
			exitInterpreter();
		} catch (...) {
			LOG(ERROR) << "An exception occured when calling beforeEnteringStates on monitors";
		}
		monIter++;
	}

	for (int i = 0; i < statesToEnter.size(); i++) {
		Element<std::string> stateElem = (Element<std::string>)statesToEnter[i];
		_configuration.push_back(stateElem);
		_statesToInvoke.push_back(stateElem);
		if (_binding == LATE && stateElem.getAttribute("isFirstEntry").size() > 0) {
			NodeSet<std::string> dataModelElems = filterChildElements(_xmlNSPrefix + "datamodel", stateElem);
			if(dataModelElems.size() > 0 && _dataModel) {
				Arabica::XPath::NodeSet<std::string> dataElems = filterChildElements(_xmlNSPrefix + "data", dataModelElems[0]);
				for (int j = 0; j < dataElems.size(); j++) {
					if (dataElems[j].getNodeType() == Node_base::ELEMENT_NODE)
						initializeData(Element<std::string>(dataElems[j]));
				}
			}
			stateElem.setAttribute("isFirstEntry", "");
		}
		// execute onentry executable content
		NodeSet<std::string> onEntryElems = filterChildElements(_xmlNSPrefix + "onEntry", stateElem);
		executeContent(onEntryElems);

		if (isMember(stateElem, statesForDefaultEntry)) {
			// execute initial transition content for compound states
			Arabica::XPath::NodeSet<std::string> transitions = _xpath.evaluate("" + _xpathPrefix + "initial/" + _xpathPrefix + "transition", stateElem).asNodeSet();
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

	monIter = _monitors.begin();
	while(monIter != _monitors.end()) {
		try {
			(*monIter)->afterEnteringStates(shared_from_this());
		} catch (Event e) {
			LOG(ERROR) << "Syntax error when calling afterEnteringStates on monitors: " << std::endl << e << std::endl;
		} catch (boost::bad_weak_ptr e) {
			LOG(ERROR) << "Unclean shutdown " << std::endl << std::endl;
			return;
		} catch (...) {
			LOG(ERROR) << "An exception occured when calling afterEnteringStates on monitors";
		}
		monIter++;
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
			NodeSet<std::string> transitions = filterChildElements(_xmlNSPrefix + "transition", state);
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