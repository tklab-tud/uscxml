#include "InterpreterDraft6.h"

#include <glog/logging.h>

namespace uscxml {

using namespace Arabica::XPath;
using namespace Arabica::DOM;

// see: http://www.w3.org/TR/scxml/#AlgorithmforSCXMLInterpretation
void InterpreterDraft6::interpret() {
	if (!_isInitialized)
		init();

	if (!_scxml)
		return;
//  dump();

	_sessionId = getUUID();

	std::string datamodelName;
	if (datamodelName.length() == 0 && HAS_ATTR(_scxml, "datamodel"))
		datamodelName = ATTR(_scxml, "datamodel");
	if (datamodelName.length() == 0 && HAS_ATTR(_scxml, "profile")) // SCION SCXML uses profile to specify datamodel
		datamodelName = ATTR(_scxml, "profile");
	if(datamodelName.length() > 0)
		_dataModel = Factory::createDataModel(datamodelName, this);
	if(datamodelName.length() > 0  && !_dataModel) {
		LOG(ERROR) << "No datamodel for " << datamodelName << " registered";
	}

	if (_dataModel) {
		_dataModel.assign("_x.args", _cmdLineOptions);
		if (_httpServlet) {
			Data data;
			data.compound["location"] = Data(_httpServlet->getURL(), Data::VERBATIM);
			_dataModel.assign("_ioprocessors['http']", data);
		}
	}

	setupIOProcessors();

	_running = true;
	_binding = (HAS_ATTR(_scxml, "binding") && boost::iequals(ATTR(_scxml, "binding"), "late") ? LATE : EARLY);

	// @TODO: Reread http://www.w3.org/TR/scxml/#DataBinding

	if (_dataModel && _binding == EARLY) {
		// initialize all data elements
		NodeSet<std::string> dataElems = _xpath.evaluate("//" + _xpathPrefix + "data", _scxml).asNodeSet();
		for (unsigned int i = 0; i < dataElems.size(); i++) {
			initializeData(dataElems[i]);
		}
	} else if(_dataModel) {
		// initialize current data elements
		NodeSet<std::string> topDataElems = filterChildElements(_xmlNSPrefix + "data", filterChildElements(_xmlNSPrefix + "datamodel", _scxml));
		for (unsigned int i = 0; i < topDataElems.size(); i++) {
			initializeData(topDataElems[i]);
		}
	}

	// executeGlobalScriptElements
	NodeSet<std::string> globalScriptElems = _xpath.evaluate("/" + _xpathPrefix + "script", _scxml).asNodeSet();
	for (unsigned int i = 0; i < globalScriptElems.size(); i++) {
		if (_dataModel)
			executeContent(globalScriptElems[i]);
	}

	NodeSet<std::string> initialTransitions;

	if (_userDefinedStartConfiguration.size() == 0) {
		// try to get initial transition form initial element
		initialTransitions = _xpath.evaluate("/" + _xpathPrefix + "initial/" + _xpathPrefix + "transition", _scxml).asNodeSet();
	}

	if (initialTransitions.size() == 0) {
		Arabica::XPath::NodeSet<std::string> initialStates;
		if (_userDefinedStartConfiguration.size() > 0) {
			// otherwise use user supplied config
			initialTransitions = getStates(_userDefinedStartConfiguration);
		} else {
			// or fetch per draft
			initialStates = getInitialStates();
		}

		assert(initialStates.size() > 0);
		for (int i = 0; i < initialStates.size(); i++) {
			Arabica::DOM::Element<std::string> initialElem = _document.createElementNS(_nsURL, "initial");
			initialElem.setAttribute("generated", "true");
			Arabica::DOM::Element<std::string> transitionElem = _document.createElementNS(_nsURL, "transition");
			transitionElem.setAttribute("target", ATTR(initialStates[i], "id"));
			initialElem.appendChild(transitionElem);
			_scxml.appendChild(initialElem);
			initialTransitions.push_back(transitionElem);
		}
	}

	assert(initialTransitions.size() > 0);
	enterStates(initialTransitions);

//  assert(hasLegalConfiguration());
	mainEventLoop();

	if (_parentQueue) {
		// send one final event to unblock eventual listeners
		Event quit;
		quit.name = "done.state.scxml";
		_parentQueue->push(quit);
	}

	// set datamodel to null from this thread
	if(_dataModel)
		_dataModel = DataModel();

}

/**
 * Called with a single data element from the topmost datamodel element.
 */
void InterpreterDraft6::initializeData(const Arabica::DOM::Node<std::string>& data) {
	if (!_dataModel) {
		LOG(ERROR) << "Cannot initialize data when no datamodel is given!";
		return;
	}
	try {
		if (!HAS_ATTR(data, "id")) {
			LOG(ERROR) << "Data element has no id!";
			return;
		}

		if (HAS_ATTR(data, "expr")) {
			std::string value = ATTR(data, "expr");
			_dataModel.assign(ATTR(data, "id"), value);
		} else if (HAS_ATTR(data, "src")) {
			URL srcURL(ATTR(data, "src"));
			if (!srcURL.isAbsolute())
				toAbsoluteURI(srcURL);

			std::stringstream ss;
			if (_cachedURLs.find(srcURL.asString()) != _cachedURLs.end()) {
				ss << _cachedURLs[srcURL.asString()];
			} else {
				ss << srcURL;
				_cachedURLs[srcURL.asString()] = srcURL;
			}
			_dataModel.assign(ATTR(data, "id"), ss.str());

		} else if (data.hasChildNodes()) {
			// search for the text node with the actual script
			NodeList<std::string> dataChilds = data.getChildNodes();
			for (int i = 0; i < dataChilds.getLength(); i++) {
				if (dataChilds.item(i).getNodeType() == Node_base::TEXT_NODE) {
					Data value = Data(dataChilds.item(i).getNodeValue());
					_dataModel.assign(ATTR(data, "id"), value);
					break;
				}
			}
		} else {
			_dataModel.assign(ATTR(data, "id"), "undefined");
		}

	} catch (Event e) {
		LOG(ERROR) << "Syntax error in data element:" << std::endl << e << std::endl;
	}
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
					(*monIter)->beforeMicroStep(this);
				} catch (Event e) {
					LOG(ERROR) << "Syntax error when calling beforeMicroStep on monitors: " << std::endl << e << std::endl;
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
						(*monIter)->beforeTakingTransitions(this, enabledTransitions);
					} catch (Event e) {
						LOG(ERROR) << "Syntax error when calling beforeTakingTransitions on monitors: " << std::endl << e << std::endl;
					} catch (...) {
						LOG(ERROR) << "An exception occured when calling beforeTakingTransitions on monitors";
					}
					monIter++;
				}
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
				(*monIter)->onStableConfiguration(this);
			} catch (Event e) {
				LOG(ERROR) << "Syntax error when calling onStableConfiguration on monitors: " << std::endl << e << std::endl;
			} catch (...) {
				LOG(ERROR) << "An exception occured when calling onStableConfiguration on monitors";
			}
			monIter++;
		}
//    }

		// whenever we have a stable configuration, run the mainThread hooks with 200fps
		while(_externalQueue.isEmpty() && _thread == NULL) {
			runOnMainThread(200);
		}

		_currEvent = _externalQueue.pop();
#if VERBOSE
		std::cout << "Received externalEvent event " << _currEvent.name << std::endl;
#endif
		_currEvent.type = Event::EXTERNAL; // make sure it is set to external
		if (!_running)
			exitInterpreter();

		if (_dataModel && boost::iequals(_currEvent.name, "cancel.invoke." + _sessionId))
			break;

		if (_dataModel)
			try {
				_dataModel.setEvent(_currEvent);
			} catch (Event e) {
				LOG(ERROR) << "Syntax error while setting external event:" << std::endl << e << std::endl;
			}
		for (unsigned int i = 0; i < _configuration.size(); i++) {
			NodeSet<std::string> invokes = filterChildElements(_xmlNSPrefix + "invoke", _configuration[i]);
			for (unsigned int j = 0; j < invokes.size(); j++) {
				Arabica::DOM::Element<std::string> invokeElem = (Arabica::DOM::Element<std::string>)invokes[j];
				std::string invokeId;
				if (HAS_ATTR(invokeElem, "id"))
					invokeId = ATTR(invokeElem, "id");
				if (HAS_ATTR(invokeElem, "idlocation") && _dataModel)
					invokeId = _dataModel.evalAsString(ATTR(invokeElem, "idlocation"));

				std::string autoForward = invokeElem.getAttribute("autoforward");
				if (boost::iequals(invokeId, _currEvent.invokeid)) {

					Arabica::XPath::NodeSet<std::string> finalizes = filterChildElements(_xmlNSPrefix + "finalize", invokeElem);
					for (int k = 0; k < finalizes.size(); k++) {
						Arabica::DOM::Element<std::string> finalizeElem = Arabica::DOM::Element<std::string>(finalizes[k]);
						executeContent(finalizeElem);
					}

				}
				if (boost::iequals(autoForward, "true")) {
					try {
						_invokers[invokeId].send(_currEvent);
					} catch(...) {
						LOG(ERROR) << "Exception caught while sending event to invoker " << invokeId;
					}
				}
			}
		}
		enabledTransitions = selectTransitions(_currEvent.name);
		if (!enabledTransitions.empty())
			microstep(enabledTransitions);
	}
	monIter = _monitors.begin();
	while(monIter != _monitors.end()) {
		try {
			(*monIter)->beforeCompletion(this);
		} catch (Event e) {
			LOG(ERROR) << "Syntax error when calling beforeCompletion on monitors: " << std::endl << e << std::endl;
		} catch (...) {
			LOG(ERROR) << "An exception occured when calling beforeCompletion on monitors";
		}
		monIter++;
	}

	exitInterpreter();
	if (_sendQueue) {
		std::map<std::string, std::pair<Interpreter*, SendRequest> >::iterator sendIter = _sendIds.begin();
		while(sendIter != _sendIds.end()) {
			_sendQueue->cancelEvent(sendIter->first);
			sendIter++;
		}
	}
	
	monIter = _monitors.begin();
	while(monIter != _monitors.end()) {
		try {
			(*monIter)->afterCompletion(this);
		} catch (Event e) {
			LOG(ERROR) << "Syntax error when calling afterCompletion on monitors: " << std::endl << e << std::endl;
		} catch (...) {
			LOG(ERROR) << "An exception occured when calling afterCompletion on monitors";
		}
		monIter++;
	}

}

Arabica::XPath::NodeSet<std::string> InterpreterDraft6::selectTransitions(const std::string& event) {
	Arabica::XPath::NodeSet<std::string> enabledTransitions;

	NodeSet<std::string> atomicStates;
	for (unsigned int i = 0; i < _configuration.size(); i++) {
		if (isAtomic(_configuration[i]))
			atomicStates.push_back(_configuration[i]);
	}
	atomicStates.to_document_order();

	for (unsigned int i = 0; i < atomicStates.size(); i++) {
		NodeSet<std::string> ancestors = getProperAncestors(atomicStates[i], Arabica::DOM::Node<std::string>());

		NodeSet<std::string> sortedAncestors;
		sortedAncestors.push_back(atomicStates[i]);
		sortedAncestors.insert(sortedAncestors.end(), ancestors.begin(), ancestors.end());

		for (unsigned int j = 0; j < sortedAncestors.size(); j++) {
			NodeSet<std::string> transitions = filterChildElements(_xmlNSPrefix + "transition", sortedAncestors[j]);
			for (unsigned int k = 0; k < transitions.size(); k++) {
				std::string eventName;
				if (HAS_ATTR(transitions[k], "event")) {
					eventName = ATTR(transitions[k], "event");
				} else if(HAS_ATTR(transitions[k], "eventexpr")) {
					if (_dataModel) {
						eventName = _dataModel.evalAsString(ATTR(transitions[k], "eventexpr"));
					} else {
						LOG(ERROR) << "Transition has eventexpr attribute with no datamodel defined";
						goto LOOP;
					}
				} else {
					goto LOOP;
				}

				if (eventName.length() > 0 &&
				        nameMatch(eventName, event) &&
				        hasConditionMatch(transitions[k])) {
					enabledTransitions.push_back(transitions[k]);
					goto LOOP;
				}
			}
		}
LOOP:
		;
	}

	enabledTransitions = filterPreempted(enabledTransitions);
	return enabledTransitions;
}

Arabica::XPath::NodeSet<std::string> InterpreterDraft6::selectEventlessTransitions() {
	Arabica::XPath::NodeSet<std::string> enabledTransitions;

	NodeSet<std::string> atomicStates;
	for (unsigned int i = 0; i < _configuration.size(); i++) {
		if (isAtomic(_configuration[i]))
			atomicStates.push_back(_configuration[i]);
	}
	atomicStates.to_document_order();

	for (unsigned int i = 0; i < atomicStates.size(); i++) {
		NodeSet<std::string> ancestors = getProperAncestors(atomicStates[i], Arabica::DOM::Node<std::string>());
		ancestors.push_back(atomicStates[i]);
		for (unsigned int j = 0; j < ancestors.size(); j++) {
			NodeSet<std::string> transitions = filterChildElements(_xmlNSPrefix + "transition", ancestors[j]);
			for (unsigned int k = 0; k < transitions.size(); k++) {
				if (!HAS_ATTR(transitions[k], "event") && hasConditionMatch(transitions[k])) {
					enabledTransitions.push_back(transitions[k]);
					goto LOOP;
				}
			}

#if 0
			NodeSet<std::string> transitions = filterChildElements(_xmlNSPrefix + "transition", ancestors[j]);
			for (unsigned int k = 0; k < transitions.size(); k++) {
				if (!((Arabica::DOM::Element<std::string>)transitions[k]).hasAttribute("event") && hasConditionMatch(transitions[k])) {
					enabledTransitions.push_back(transitions[k]);
					goto LOOP;
				}
			}
#endif
		}
LOOP:
		;
	}

	enabledTransitions = filterPreempted(enabledTransitions);
	return enabledTransitions;
}

Arabica::XPath::NodeSet<std::string> InterpreterDraft6::filterPreempted(const Arabica::XPath::NodeSet<std::string>& enabledTransitions) {
	Arabica::XPath::NodeSet<std::string> filteredTransitions;
	for (unsigned int i = 0; i < enabledTransitions.size(); i++) {
		Arabica::DOM::Node<std::string> t = enabledTransitions[i];
		for (unsigned int j = i+1; j < enabledTransitions.size(); j++) {
			Arabica::DOM::Node<std::string> t2 = enabledTransitions[j];
			if (isPreemptingTransition(t2, t)) {
#if VERBOSE
				std::cout << "Transition preempted!: " << std::endl << t2 << std::endl << t << std::endl;
#endif
				goto LOOP;
			}
		}
		filteredTransitions.push_back(t);
LOOP:
		;
	}
	return filteredTransitions;
}

bool InterpreterDraft6::isPreemptingTransition(const Arabica::DOM::Node<std::string>& t1, const Arabica::DOM::Node<std::string>& t2) {
	assert(t1);
	assert(t2);

#if VERBOSE
	std::cout << "Checking preemption: " << std::endl << t1 << std::endl << t2 << std::endl;
#endif

#if 1
	if (t1 == t2)
		return false;
	if (isWithinSameChild(t1) && (!isTargetless(t2) && !isWithinSameChild(t2)))
		return true;
	if (!isTargetless(t1) && !isWithinSameChild(t1))
		return true;
	return false;
#endif

}

void InterpreterDraft6::microstep(const Arabica::XPath::NodeSet<std::string>& enabledTransitions) {
#if 0
	std::cout << "Transitions: ";
	for (int i = 0; i < enabledTransitions.size(); i++) {
		std::cout << ((Arabica::DOM::Element<std::string>)getSourceState(enabledTransitions[i])).getAttribute("id") << " -> " << std::endl;
		NodeSet<std::string> targetSet = getTargetStates(enabledTransitions[i]);
		for (int j = 0; j < targetSet.size(); j++) {
			std::cout << "    " << ((Arabica::DOM::Element<std::string>)targetSet[j]).getAttribute("id") << std::endl;
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
	statesToExit.to_document_order();
	statesToExit.reverse();

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
		Arabica::DOM::Element<std::string> transition = ((Arabica::DOM::Element<std::string>)enabledTransitions[i]);
		if (!isTargetless(transition)) {
			std::string transitionType = (boost::iequals(transition.getAttribute("type"), "internal") ? "internal" : "external");
			NodeSet<std::string> tStates = getTargetStates(transition);
			Arabica::DOM::Node<std::string> ancestor;
			Arabica::DOM::Node<std::string> source = getSourceState(transition);

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

#if VERBOSE
	std::cout << "States to exit: ";
	for (int i = 0; i < statesToExit.size(); i++) {
		std::cout << LOCALNAME(statesToExit[i]) << ":" << ATTR(statesToExit[i], "id") << ", ";
	}
	std::cout << std::endl;

#endif

	// remove statesToExit from _statesToInvoke
	std::list<Arabica::DOM::Node<std::string> > tmp;
	for (int i = 0; i < _statesToInvoke.size(); i++) {
		if (!isMember(_statesToInvoke[i], statesToExit)) {
			tmp.push_back(_statesToInvoke[i]);
		}
	}
	_statesToInvoke = NodeSet<std::string>();
	_statesToInvoke.insert(_statesToInvoke.end(), tmp.begin(), tmp.end());

	statesToExit.to_document_order();
	statesToExit.reverse();

	monIter = _monitors.begin();
	while(monIter != _monitors.end()) {
		try {
			(*monIter)->beforeExitingStates(this, statesToExit);
		} catch (Event e) {
			LOG(ERROR) << "Syntax error when calling beforeExitingStates on monitors: " << std::endl << e << std::endl;
		} catch (...) {
			LOG(ERROR) << "An exception occured when calling beforeExitingStates on monitors";
		}
		monIter++;
	}

	for (int i = 0; i < statesToExit.size(); i++) {
		NodeSet<std::string> histories = filterChildElements(_xmlNSPrefix + "history", statesToExit[i]);
		for (int j = 0; j < histories.size(); j++) {
			Arabica::DOM::Element<std::string> historyElem = (Arabica::DOM::Element<std::string>)histories[j];
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
			Arabica::DOM::Element<std::string> onExitElem = (Arabica::DOM::Element<std::string>)onExits[j];
			executeContent(onExitElem);
		}
		NodeSet<std::string> invokes = filterChildElements(_xmlNSPrefix + "invoke", statesToExit[i]);
		for (int j = 0; j < invokes.size(); j++) {
			Arabica::DOM::Element<std::string> invokeElem = (Arabica::DOM::Element<std::string>)invokes[j];
			cancelInvoke(invokeElem);
		}
	}

	// remove statesToExit from _configuration
	tmp.clear();
	for (int i = 0; i < _configuration.size(); i++) {
		if (!isMember(_configuration[i], statesToExit)) {
			tmp.push_back(_configuration[i]);
		}
	}
	_configuration = NodeSet<std::string>();
	_configuration.insert(_configuration.end(), tmp.begin(), tmp.end());

	monIter = _monitors.begin();
	while(monIter != _monitors.end()) {
		try {
			(*monIter)->afterExitingStates(this);
		} catch (Event e) {
			LOG(ERROR) << "Syntax error when calling afterExitingStates on monitors: " << std::endl << e << std::endl;
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
		Arabica::DOM::Element<std::string> transition = ((Arabica::DOM::Element<std::string>)enabledTransitions[i]);
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

			Arabica::DOM::Node<std::string> ancestor;
			Arabica::DOM::Node<std::string> source = getSourceState(transition);
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

	monIter = _monitors.begin();
	while(monIter != _monitors.end()) {
		try {
			(*monIter)->beforeEnteringStates(this, statesToEnter);
		} catch (Event e) {
			LOG(ERROR) << "Syntax error when calling beforeEnteringStates on monitors: " << std::endl << e << std::endl;
		} catch (...) {
			LOG(ERROR) << "An exception occured when calling beforeEnteringStates on monitors";
		}
		monIter++;
	}

	for (int i = 0; i < statesToEnter.size(); i++) {
		Arabica::DOM::Element<std::string> stateElem = (Arabica::DOM::Element<std::string>)statesToEnter[i];
		_configuration.push_back(stateElem);
		_statesToInvoke.push_back(stateElem);
		if (_binding == LATE && stateElem.getAttribute("isFirstEntry").size() > 0) {
			NodeSet<std::string> dataModelElems = filterChildElements(_xmlNSPrefix + "datamodel", stateElem);
			if(dataModelElems.size() > 0 && _dataModel) {
				Arabica::XPath::NodeSet<std::string> dataElems = filterChildElements(_xmlNSPrefix + "data", dataModelElems[0]);
				for (int j = 0; j < dataElems.size(); j++) {
					initializeData(dataElems[j]);
				}
			}
			stateElem.setAttribute("isFirstEntry", "");
		}
		// execute onentry executable content
		NodeSet<std::string> onEntryElems = filterChildElements(_xmlNSPrefix + "onEntry", stateElem);
		executeContent(onEntryElems);

		if (isMember(stateElem, statesForDefaultEntry)) {
			// execute initial transition content for compund states
			Arabica::XPath::NodeSet<std::string> transitions = _xpath.evaluate("" + _xpathPrefix + "initial/" + _xpathPrefix + "transition", stateElem).asNodeSet();
			for (int j = 0; j < transitions.size(); j++) {
				executeContent(transitions[j]);
			}
		}

		if (isFinal(stateElem)) {
			internalDoneSend(stateElem);
			Arabica::DOM::Element<std::string> parent = (Arabica::DOM::Element<std::string>)stateElem.getParentNode();

			if (isParallel(parent.getParentNode())) {
				Arabica::DOM::Element<std::string> grandParent = (Arabica::DOM::Element<std::string>)parent.getParentNode();

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
		Arabica::DOM::Element<std::string> stateElem = (Arabica::DOM::Element<std::string>)_configuration[i];
		if (isFinal(stateElem) && parentIsScxmlState(stateElem)) {
			_running = false;
			_done = true;
		}
	}

	monIter = _monitors.begin();
	while(monIter != _monitors.end()) {
		try {
			(*monIter)->afterEnteringStates(this);
		} catch (Event e) {
			LOG(ERROR) << "Syntax error when calling afterEnteringStates on monitors: " << std::endl << e << std::endl;
		} catch (...) {
			LOG(ERROR) << "An exception occured when calling afterEnteringStates on monitors";
		}
		monIter++;
	}

}

void InterpreterDraft6::addStatesToEnter(const Arabica::DOM::Node<std::string>& state,
        Arabica::XPath::NodeSet<std::string>& statesToEnter,
        Arabica::XPath::NodeSet<std::string>& statesForDefaultEntry) {
	std::string stateId = ((Arabica::DOM::Element<std::string>)state).getAttribute("id");

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