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

#include "uscxml/transform/ChartToFSM.h"
#include <DOM/io/Stream.hpp>
#include <glog/logging.h>

#include <iostream>
#include "uscxml/UUID.h"
#include <math.h>
#include <string.h>
#include <algorithm>
#include <limits>

namespace uscxml {


using namespace Arabica::DOM;
using namespace Arabica::XPath;

#define CREATE_TRANSIENT_STATE_WITH_CHILDS \
if (childs.size() > 0) { \
	Element<std::string> transientState = _flatDoc.createElementNS(_nsInfo.nsURL, "state"); \
	_nsInfo.setPrefix(transientState);\
	transientState.setAttribute("transient", "true"); \
	for (int i = 0; i < childs.size(); i++) { \
		Node<std::string> imported = _flatDoc.importNode(childs[i], true); \
		transientState.appendChild(imported); \
	} \
	transientStateChain.push_back(transientState); \
} \
childs = NodeSet<std::string>();

Interpreter ChartToFSM::flatten(const Interpreter& other) {

	// instantiate a new InterpreterImpl to do the flattening
	boost::shared_ptr<InterpreterImpl> flattener = boost::shared_ptr<InterpreterImpl>(new FlatteningInterpreter(other.getDocument()));
	flattener->setNameSpaceInfo(other.getNameSpaceInfo());
	flattener->interpret();

	// clone the flattener implementation to a new interpreter
	Interpreter flat = Interpreter::fromClone(flattener);
	return flat;
}


FlatteningInterpreter::FlatteningInterpreter(const Document<std::string>& doc) {

	_currGlobalTransition = NULL;

	// just copy given doc into _document an create _flatDoc for the FSM
	DOMImplementation<std::string> domFactory = Arabica::SimpleDOM::DOMImplementation<std::string>::getDOMImplementation();
	_document = domFactory.createDocument(doc.getNamespaceURI(), "", 0);
	_flatDoc = domFactory.createDocument(doc.getNamespaceURI(), "", 0);

	Node<std::string> child = doc.getFirstChild();
	while (child) {
		Node<std::string> newNode = _document.importNode(child, true);
		_document.appendChild(newNode);
		child = child.getNextSibling();
	}

	addMonitor(this);
}

FlatteningInterpreter::~FlatteningInterpreter() {
	std::map<std::string, GlobalState*>::iterator confIter = _globalConf.begin();
	while(confIter != _globalConf.end()) {
		std::map<std::string, GlobalTransition*>::iterator transIter = confIter->second->outgoing.begin();
		while (transIter != confIter->second->outgoing.end()) {
			delete transIter->second;
			transIter++;
		}
		delete confIter->second;
		confIter++;
	}

}

Document<std::string> FlatteningInterpreter::getDocument() const {
//	std::cout << "######################" << std::endl;
//	std::cout << _flatDoc << std::endl;
//	std::cout << "######################" << std::endl;
	return _flatDoc;
}

void FlatteningInterpreter::interpret() {

	init();
	setupIOProcessors();

	// initialize the datamodel
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

	_binding = (HAS_ATTR(_scxml, "binding") && iequals(ATTR(_scxml, "binding"), "late") ? LATE : EARLY);

	// reset
	_globalConf.clear();
	_currGlobalTransition = NULL;

	// very first state
	_start = new GlobalState(_configuration, _alreadyEntered, _historyValue);
	_globalConf[_start->stateId] = _start;

	NodeSet<std::string> initialTransitions;

	// enter initial configuration
	Arabica::XPath::NodeSet<std::string> initialStates;
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
	labelTransitions();
	weightTransitions();

//	std::cout << _scxml << std::endl;

	GlobalTransition* globalTransition = new GlobalTransition(initialTransitions, _dataModel);
	_start->outgoing[globalTransition->transitionId] = globalTransition;
	globalTransition->source = _start->stateId;
	_currGlobalTransition = globalTransition;

	enterStates(initialTransitions);
	explode();

#if 0
	// print set of global configurations
	for(std::map<std::string, GlobalState*>::iterator globalConfIter = _globalConf.begin();
	        globalConfIter != _globalConf.end();
	        globalConfIter++) {
		std::cout << globalConfIter->first << std::endl;
	}
	std::cout << _globalConf.size() << std::endl;
#endif

	createDocument();
}

void FlatteningInterpreter::executeContent(const Arabica::DOM::Node<std::string>& content, bool rethrow) {
//	std::cout << content << std::endl;
	GlobalTransition::Action action;

	if (false) {
	} else if (TAGNAME(content) == "transition") {
		action.transition = content;
	} else if (TAGNAME(content) == "onexit") {
		action.onExit = content;
	} else if (TAGNAME(content) == "onentry") {
		action.onExit = content;
	} else {
		assert(false);
	}
	_currGlobalTransition->actions.push_back(action);
}

void FlatteningInterpreter::executeContent(const Arabica::DOM::NodeList<std::string>& content, bool rethrow) {
	for (int i = 0; i < content.getLength(); i++) {
		executeContent(content.item(i));
	}
	assert(false);
}

void FlatteningInterpreter::executeContent(const Arabica::XPath::NodeSet<std::string>& content, bool rethrow) {
	for (int i = 0; i < content.size(); i++) {
		executeContent(content[i]);
	}
}

void FlatteningInterpreter::invoke(const Arabica::DOM::Node<std::string>& element) {
	GlobalTransition::Action action;
	action.invoke = element;
	_currGlobalTransition->actions.push_back(action);
	_currGlobalTransition->invoke.push_back(element);
}

void FlatteningInterpreter::cancelInvoke(const Arabica::DOM::Node<std::string>& element) {
	GlobalTransition::Action action;
	action.uninvoke = element;
	_currGlobalTransition->actions.push_back(action);
	_currGlobalTransition->uninvoke.push_back(element);
}

void FlatteningInterpreter::internalDoneSend(const Arabica::DOM::Node<std::string>& state) {

	if (!isState(state))
		return;
	Arabica::DOM::Element<std::string> stateElem = (Arabica::DOM::Element<std::string>)state;

//	if (parentIsScxmlState(state))
//		return;

//	std::cout << "internalDoneSend: " << state << std::endl;

	// create onentry with a raise element
	Element<std::string> onentry = _flatDoc.createElementNS(_nsInfo.nsURL, "onentry");
	_nsInfo.setPrefix(onentry);

	Element<std::string> raise = _flatDoc.createElementNS(_nsInfo.nsURL, "raise");
	_nsInfo.setPrefix(raise);

	onentry.appendChild(raise);

	Arabica::XPath::NodeSet<std::string> doneDatas = filterChildElements(_nsInfo.xmlNSPrefix + "donedata", stateElem);
	if (doneDatas.size() > 0) {
		Arabica::DOM::Node<std::string> doneData = doneDatas[0];
		Arabica::XPath::NodeSet<std::string> contents = filterChildElements(_nsInfo.xmlNSPrefix + "content", doneDatas[0]);
		if (contents.size() > 0) {
			Node<std::string> imported = _flatDoc.importNode(contents[0], true);
			raise.appendChild(imported);
		}
		Arabica::XPath::NodeSet<std::string> params = filterChildElements(_nsInfo.xmlNSPrefix + "param", doneDatas[0]);
		if (params.size() > 0) {
			Node<std::string> imported = _flatDoc.importNode(params[0], true);
			raise.appendChild(imported);
		}
	}

	raise.setAttribute("event", "done.state." + ATTR(stateElem.getParentNode(), "id")); // parent?!

	GlobalTransition::Action action;
	action.onEntry = onentry;

	_currGlobalTransition->actions.push_back(action);

}

static bool isSuperset(const GlobalTransition* t1, const GlobalTransition* t2) {
	bool isSuperset = true;

	if (t1->transitions.size() >= t2->transitions.size())
		return false;

	for (int i = 0; i < t1->transitions.size(); i++) {
		if (!InterpreterImpl::isMember(t1->transitions[i], t2->transitions)) {
			isSuperset = false;
		}
	}
	return isSuperset;
}

static NodeSet<std::string> filterChildEnabled(const NodeSet<std::string>& transitions) {
	// drop any transition that is already enabled by a child
	NodeSet<std::string> filteredTransitions;
	for (unsigned int i = 0; i < transitions.size(); i++) {
		Node<std::string> t1 = transitions[i];
		Node<std::string> p1 = InterpreterImpl::getParentState(t1);
		for (unsigned int j = 0; j < transitions.size(); j++) {
			if (i == j)
				continue;
			Node<std::string> t2 = transitions[j];
			Node<std::string> p2 = InterpreterImpl::getParentState(t2);
//			p2 = p2.getParentNode();
			while(p2) {
				if (p1 == p2) {
					std::string eventDesc1 = ATTR(t1, "event");
					std::string eventDesc2 = ATTR(t2, "event");
					if (InterpreterImpl::nameMatch(eventDesc1, eventDesc2)) {
//						std::cout << "Dropping " << t1 << std::endl << "for " << t2 << std::endl;
						goto SKIP_TRANSITION;
					}
				}
				p2 = p2.getParentNode();
			}
		}
		filteredTransitions.push_back(t1);
SKIP_TRANSITION:
		;
	}
	return filteredTransitions;
}

static std::list<GlobalTransition*> sortTransitions(std::list<GlobalTransition*> list) {
	bool stable = false;
	while(!stable) {
		for (std::list<GlobalTransition*>::iterator outerIter = list.begin();
		        outerIter != list.end();
		        outerIter++) {
			for (std::list<GlobalTransition*>::iterator innerIter = outerIter;
			        innerIter != list.end();
			        innerIter++) {
				GlobalTransition* t1 = *outerIter;
				GlobalTransition* t2 = *innerIter;

				if (isSuperset(t1, t2)) {
//					std::cout << "swapping " << t1->transitionId << " / " << t2->transitionId << std::endl;
					std::swap(*innerIter, *outerIter);
					goto NEXT_ITER;
				}
				for (int i = t1->firstElemPerLevel.size() - 1; i >= 0 ; i--) {
					if (t1->firstElemPerLevel[i] == std::numeric_limits<int32_t>::max() || t2->firstElemPerLevel[i] == std::numeric_limits<int32_t>::max())
						break;
					if (t1->firstElemPerLevel[i] > t2->firstElemPerLevel[i]) {
//						std::cout << "swapping at " << i << " " << t1->transitionId << " / " << t2->transitionId << std::endl;
						std::swap(*innerIter, *outerIter);
						goto NEXT_ITER;
					} else {
						break;
					}
				}
			}
		}
		stable = true;
NEXT_ITER:
		;
	}
	return list;
}



void FlatteningInterpreter::explode() {

	// save global configuration elements to restore after recursive explode
	Arabica::XPath::NodeSet<std::string> configuration = _configuration;
	Arabica::XPath::NodeSet<std::string> alreadyEntered = _alreadyEntered;
	std::map<std::string, Arabica::XPath::NodeSet<std::string> > historyValue = _historyValue;

	// create current state from global configuration
	GlobalState* globalState = new GlobalState(configuration, alreadyEntered, historyValue);

	// remember that the last transition lead here
	if (_currGlobalTransition) {
		_currGlobalTransition->destination = globalState->stateId;
		globalState->incoming[_currGlobalTransition->transitionId] = _currGlobalTransition;

//		if (!_currGlobalTransition->isEventless) {
		// if it was an eventful transition, add all invokers
		for (unsigned int i = 0; i < _statesToInvoke.size(); i++) {
			NodeSet<std::string> invokes = filterChildElements(_nsInfo.xmlNSPrefix + "invoke", _statesToInvoke[i]);
			for (unsigned int j = 0; j < invokes.size(); j++) {
				invoke(invokes[j]);
			}
		}
		_statesToInvoke = NodeSet<std::string>();
//		}
	}

	if (_globalConf.find(globalState->stateId) != _globalConf.end()) {
		delete globalState;
		return; // we have already been here
	}
	_globalConf[globalState->stateId] = globalState;

	// get all transition elements from states in the current configuration
	NodeSet<std::string> allTransitions = filterChildElements(_nsInfo.xmlNSPrefix + "transition", configuration);

	/**
	 * From http://www.w3.org/TR/scxml/#SelectingTransitions
	 *
	 * A transition T is enabled by named event E in atomic state S if
	 *   a) T's source state is S or an ancestor of S
	 *   b) T matches E's name
	 *   c) T lacks a 'cond' attribute or its 'cond' attribute evaluates to "true"
	 *
	 * A transition is enabled by NULL in atomic state S if
	 *   a) T lacks an 'event' attribute
	 *   b) T's source state is S or an ancestor of S
	 *   c) T lacks an 'cond' attribute or its 'cond' attribute evaluates to "true"
	 *
	 * The _source state_ of a transition is the <state> or <parallel> element that it occurs in.
	 * The _target state(s)_ of the transition is the state or set of states specified by its 'target' attribute.
	 * The _complete target_ set of a transition consists of all the states that will be active after the transition is taken.
	 *
	 * A transition T is optimally enabled by event E in atomic state S if
	 *   a) T is enabled by E in S
	 *   b) no transition that precedes T in document order in T's source state is enabled by E in S
	 *   c) no transition is enabled by E in S in any descendant of T's source state.
	 *
	 * Two transitions T1 and T2 conflict in state configuration C if their exit sets in C have a non-null intersection.
	 *   let transitions T1 and T2 conflict:
	 *     T1 is optimally enabled in atomic state S1
	 *     T2 is optimally enabled in atomic state S2
	 *     S1 and S2 are both active
	 *   T1 has a higher priority than T2 if:
	 *     a) T1's source state is a descendant of T2's source state, or
	 *     b) S1 precedes S2 in document order
	 *
	 * The _optimal transition set_ enabled by event E in state configuration C is
	 * the largest set of transitions such that:
	 *   a) each transition in the set is optimally enabled by E in an atomic state in C
	 *   b) no transition conflicts with another transition in the set
	 *   c) there is no optimally enabled transition outside the set that has a higher priority than some member of the set
	 *
	 * A _microstep_ consists of the execution of the transitions in an optimal enabled transition set
	 *
	 * A _macrostep_ is a series of one or more microsteps ending in a configuration
	 * where the internal event queue is empty and no transitions are enabled by NULL
	 */


	if (allTransitions.size() == 0)
		return; // no transitions

	int nrElements = allTransitions.size();
	int k = 0;
	int* stack = (int*)malloc((nrElements + 1) * sizeof(int));
	memset(stack, 0, (nrElements + 1) * sizeof(int));

	// subset of powerset we already processed
	std::map<std::string, GlobalTransition*> transitionSets;

	while(1) {
		// create the power set of all potential transitions
		// see: http://www.programminglogic.com/powerset-algorithm-in-c/

		if (stack[k] < nrElements) {
			stack[k+1] = stack[k] + 1;
			k++;
		}

		else {
			stack[k-1]++;
			k--;
		}

		if (k==0)
			break;

		NodeSet<std::string> transitions;
		for (int i = 1; i <= k; i++) {
			transitions.push_back(allTransitions[stack[i] - 1]);
		}

		// remove those transitions with a child transition
		transitions = filterChildEnabled(transitions);

		// reduce to conflict-free subset
		transitions = filterPreempted(transitions);

		// algorithm can never reduce to empty set
		assert(transitions.size() > 0);

		// create a GlobalTransition object from the set
		GlobalTransition* transition = new GlobalTransition(transitions, _dataModel);
		if (!transition->isValid) {
			// this set of transitions can not be enabled together
			delete transition;
			continue;
		}

		// two combinations might have projected onto the same conflict-free set
		if (transitionSets.find(transition->transitionId) != transitionSets.end()) {
//			std::cout << "skipping as projected onto existing conflict-free subset" << std::endl;
			delete transition;
			continue;
		}

		for (int currDepth = 0; currDepth <= maxDepth; currDepth++) {
			int lowestOrder = std::numeric_limits<int32_t>::max();
			int nrDepth = 0;
			int prioPerLevel = 0;
			for (int i = 0; i < transitions.size(); i++) {
				int depth = strTo<int>(ATTR(transitions[i], "depth"));
				if (depth != currDepth)
					continue;
				nrDepth++;
				int order = strTo<int>(ATTR(transitions[i], "order"));
				if (order < lowestOrder)
					lowestOrder = order;
				prioPerLevel += pow(maxOrder, maxOrder - order);
			}
			transition->nrElemPerLevel.push_back(nrDepth);
			transition->firstElemPerLevel.push_back(lowestOrder);
			transition->prioPerLevel.push_back(prioPerLevel);
		}

#if 0
		// calculate priority
		transition->priority = 0;
		for (int currDepth = maxDepth; currDepth >= 0; currDepth--) {
			// what's the deepest depth of this set?
			for (int i = 0; i < transitions.size(); i++) {
				int depth = strTo<int>(ATTR(transitions[i], "depth"));
				if (depth == currDepth) {
					int highestOrder = 0;
					// what's the highest order at this depth?
					for (int j = 0; j < transitions.size(); j++) {
						int order = strTo<int>(ATTR(transitions[j], "order"));
						if (order > highestOrder)
							highestOrder = order;
					}
					transition->priority += pow(maxOrder + 1, currDepth); // + (maxOrder - highestOrder);
					goto NEXT_DEPTH;
				}
			}
NEXT_DEPTH:
			;
		}
#endif
		// remember this conflict-free set
//		std::cout << "New conflict-free subset: " << transition->transitionId << ":" << transition->eventDesc << std::endl;
		transitionSets[transition->transitionId] = transition;
	}

	// TODO: reduce and sort transition sets
	std::list<GlobalTransition*> transitionList;
	for(std::map<std::string, GlobalTransition*>::iterator transSetIter = transitionSets.begin();
	        transSetIter != transitionSets.end();
	        transSetIter++) {
		transitionList.push_back(transSetIter->second);
	}

	for(std::list<GlobalTransition*>::iterator transListIter = transitionList.begin();
	        transListIter != transitionList.end();
	        transListIter++) {

		// add transition set to current global state
		globalState->outgoing[(*transListIter)->transitionId] = *transListIter;
		(*transListIter)->source = globalState->stateId;

		_currGlobalTransition = *transListIter;
		microstep((*transListIter)->transitions);
		explode();

		// reset state for next transition set
		_configuration = configuration;
		_alreadyEntered = alreadyEntered;
		_historyValue = historyValue;

	}
}

void FlatteningInterpreter::createDocument() {
	Node<std::string> _origSCXML = _scxml;

	_scxml = _flatDoc.createElementNS(_nsInfo.nsURL, "scxml");
	_nsInfo.setPrefix(_scxml);

	_scxml.setAttribute("flat", "true");
	_flatDoc.appendChild(_scxml);

	if (HAS_ATTR(_origSCXML, "datamodel")) {
		_scxml.setAttribute("datamodel", ATTR(_origSCXML, "datamodel"));
	}

	if (HAS_ATTR(_origSCXML, "binding")) {
		_scxml.setAttribute("binding", ATTR(_origSCXML, "binding"));
	}

	_scxml.setAttribute("initial", _start->stateId);

	NodeSet<std::string> datas;
	if (_binding == InterpreterImpl::LATE) {
		// with late binding, just copy direct datamodel childs
		datas = filterChildElements(_nsInfo.xmlNSPrefix + "datamodel", _origSCXML);
	} else {
		// with early binding, copy all datamodel elements into scxml element
		datas = _xpath.evaluate("//" + _nsInfo.xpathPrefix + "datamodel", _origSCXML).asNodeSet();
	}
	for (int i = 0; i < datas.size(); i++) {
		if (isInEmbeddedDocument(datas[i]))
			continue; // nested document
		Node<std::string> imported = _flatDoc.importNode(datas[i], true);
		_scxml.appendChild(imported);
	}


	NodeSet<std::string> scripts = filterChildElements(_nsInfo.xmlNSPrefix + "script", _origSCXML);
	for (int i = 0; i < scripts.size(); i++) {
		Node<std::string> imported = _flatDoc.importNode(scripts[i], true);
		_scxml.appendChild(imported);
	}

	NodeSet<std::string> comments = filterChildType(Node_base::COMMENT_NODE, _origSCXML);
	for (int i = 0; i < comments.size(); i++) {
		Node<std::string> imported = _flatDoc.importNode(comments[i], true);
		_scxml.appendChild(imported);
	}

	for (std::map<std::string, GlobalState*>::iterator confIter = _globalConf.begin();
	        confIter != _globalConf.end();
	        confIter++) {
		Node<std::string> state = globalStateToNode(confIter->second);
		_scxml.appendChild(state);
	}
//	exit(0);

}

Node<std::string> FlatteningInterpreter::globalStateToNode(GlobalState* globalState) {
	Element<std::string> state = _flatDoc.createElementNS(_nsInfo.nsURL, "state");
	_nsInfo.setPrefix(state);

	state.setAttribute("id", globalState->stateId);

	if (globalState->isFinal)
		state.setAttribute("final", "true");

	std::list<GlobalTransition*> transitionList;
	for (std::map<std::string, GlobalTransition*>::iterator outIter = globalState->outgoing.begin();
	        outIter != globalState->outgoing.end();
	        outIter++) {
		transitionList.push_back(outIter->second);
	}

	transitionList = sortTransitions(transitionList);

//	std::cout << "/////////////////" << std::endl;
	for (std::list<GlobalTransition*>::iterator outIter = transitionList.begin();
	        outIter != transitionList.end();
	        outIter++) {
		state.appendChild(globalTransitionToNode(*outIter));
	}
//	std::cout << "/////////////////" << std::endl;

	return state;
}

/**
 * Creates transient states for executable content as a side-effect
 */
Node<std::string> FlatteningInterpreter::globalTransitionToNode(GlobalTransition* globalTransition) {
	Element<std::string> transition = _flatDoc.createElementNS(_nsInfo.nsURL, "transition");
	_nsInfo.setPrefix(transition);

	if (!globalTransition->isEventless) {
		transition.setAttribute("event", globalTransition->eventDesc);
	}

	if (globalTransition->condition.size() > 0) {
		transition.setAttribute("cond", globalTransition->condition);
	}

//	transition.setAttribute("priority", toStr(globalTransition->priority));

#if 0
	std::stringstream feSS;
	std::string seperator = "";
	for (int i = 0; i < globalTransition->firstElemPerLevel.size(); i++) {
		feSS << seperator << globalTransition->firstElemPerLevel[i];
		seperator = ", ";
	}
	transition.setAttribute("firstPerLevel", feSS.str());

	std::stringstream nrSS;
	seperator = "";
	for (int i = 0; i < globalTransition->nrElemPerLevel.size(); i++) {
		nrSS << seperator << globalTransition->nrElemPerLevel[i];
		seperator = ", ";
	}
	transition.setAttribute("numberPerLevel", nrSS.str());

	std::stringstream prSS;
	seperator = "";
	for (int i = 0; i < globalTransition->prioPerLevel.size(); i++) {
		prSS << seperator << globalTransition->prioPerLevel[i];
		seperator = ", ";
	}
	transition.setAttribute("prioPerLevel", nrSS.str());
#endif

	transition.setAttribute("id", globalTransition->transitionId);

//	std::cout << " firstPerLevel:" << feSS.str() << " " << globalTransition->transitionId << std::endl;
//	std::cout << "event: " << globalTransition->eventDesc << " firstPerLevel:" << feSS.str() << " numberPerLevel:" << nrSS.str() << " prioPerLevel:" << prSS.str() << " " << globalTransition->transitionId << std::endl;
//	std::cout << globalTransition->transitionId << std::endl;

	NodeSet<std::string> transientStateChain;

	// gather content for new transient state
	NodeSet<std::string> childs;

	// iterate all actions taken during the transition
	for (std::list<GlobalTransition::Action>::iterator actionIter = globalTransition->actions.begin();
	        actionIter != globalTransition->actions.end();
	        actionIter++) {

		if (actionIter->transition) {
			Element<std::string> onexit = _flatDoc.createElementNS(_nsInfo.nsURL, "onexit");
			_nsInfo.setPrefix(onexit);
			Node<std::string> child = actionIter->transition.getFirstChild();
			while(child) {
				Node<std::string> imported = _flatDoc.importNode(child, true);
				onexit.appendChild(imported);
				child = child.getNextSibling();
			}
			if (onexit.hasChildNodes())
				childs.push_back(onexit);
			continue;
		}

		if (actionIter->onExit) {
			childs.push_back(actionIter->onExit);
			continue;
		}

		if (actionIter->onEntry) {
			childs.push_back(actionIter->onEntry);
			continue;
		}

		if (actionIter->invoke) {
			if (!globalTransition->isTargetless) {
				CREATE_TRANSIENT_STATE_WITH_CHILDS
			}
			Element<std::string> invokeElem = Element<std::string>(actionIter->invoke);
			invokeElem.setAttribute("persist", "true");
			childs.push_back(invokeElem);
			continue;
		}

		if (actionIter->uninvoke) {
			Element<std::string> uninvokeElem = _flatDoc.createElementNS(_nsInfo.nsURL, "uninvoke");
			_nsInfo.setPrefix(uninvokeElem);

			if (HAS_ATTR(actionIter->uninvoke, "type")) {
				uninvokeElem.setAttribute("type", ATTR(actionIter->uninvoke, "type"));
			}
			if (HAS_ATTR(actionIter->uninvoke, "typeexpr")) {
				uninvokeElem.setAttribute("typeexpr", ATTR(actionIter->uninvoke, "typeexpr"));
			}
			if (HAS_ATTR(actionIter->uninvoke, "id")) {
				uninvokeElem.setAttribute("id", ATTR(actionIter->uninvoke, "id"));
			}
			if (HAS_ATTR(actionIter->uninvoke, "idlocation")) {
				uninvokeElem.setAttribute("idlocation", ATTR(actionIter->uninvoke, "idlocation"));
			}
			childs.push_back(uninvokeElem);
			continue;
		}

		if (actionIter->entered) {
			// we entered a new child - check if it has a datamodel and we entered for the first time
			if (_binding == InterpreterImpl::LATE) {
				NodeSet<std::string> datamodel = filterChildElements(_nsInfo.xmlNSPrefix + "datamodel", actionIter->entered);
				if (datamodel.size() > 0 && !isMember(actionIter->entered, _globalConf[globalTransition->source]->alreadyEnteredStates)) {
					childs.push_back(datamodel);
				}
			}
		}
		if (!globalTransition->isTargetless) {
			CREATE_TRANSIENT_STATE_WITH_CHILDS
		}
	}

	if (globalTransition->isTargetless) {
		for (int i = 0; i < childs.size(); i++) {
			Node<std::string> imported = _flatDoc.importNode(childs[i], true);
			transition.appendChild(imported);
		}
		return transition;
	}

	CREATE_TRANSIENT_STATE_WITH_CHILDS

	if (transientStateChain.size() > 0) {
		for (int i = 0; i < transientStateChain.size(); i++) {
			Element<std::string> transientStateElem = Element<std::string>(transientStateChain[i]);
			transientStateElem.setAttribute("id", "transient-" + globalTransition->transitionId + "-" + globalTransition->source + "-" + toStr(i));

			Element<std::string> exitTransition = _flatDoc.createElementNS(_nsInfo.nsURL, "transition");
			_nsInfo.setPrefix(exitTransition);

			if (i == transientStateChain.size() - 1) {
				exitTransition.setAttribute("target", globalTransition->destination);
			} else {
				exitTransition.setAttribute("target", "transient-" + globalTransition->transitionId + "-" + globalTransition->source + "-" + toStr(i + 1));
			}
			transientStateElem.appendChild(exitTransition);

			if (i == 0)
				transition.setAttribute("target", transientStateElem.getAttribute("id"));

			_scxml.appendChild(transientStateElem);
		}
	} else {
		transition.setAttribute("target", globalTransition->destination);
	}

	return transition;
}

void FlatteningInterpreter::weightTransitions() {
	maxDepth = 0;
	maxOrder = 0;

	int depth = 0;
	Arabica::XPath::NodeSet<std::string> states = getChildStates(_scxml);
	while(states.size() > 0) {
		NodeSet<std::string> transitions = filterChildElements(_nsInfo.xmlNSPrefix + "transition", states);
		NodeSet<std::string> initials = filterChildElements(_nsInfo.xmlNSPrefix + "initial", states);
		transitions.push_back(filterChildElements(_nsInfo.xmlNSPrefix + "transition", initials));

		for (int j = 0; j < transitions.size(); j++) {
			if (depth > maxDepth)
				maxDepth = depth;
			if (j > maxOrder)
				maxOrder = j;
			Element<std::string> transition = Element<std::string>(transitions[j]);
			transition.setAttribute("depth", toStr(depth));
			transition.setAttribute("order", toStr(j));
		}
		depth++;
		states = getChildStates(states);
	}
}

void FlatteningInterpreter::labelTransitions() {
	// put a unique id on each transition
	Arabica::XPath::NodeSet<std::string> states = getAllStates();
	states.push_back(_scxml);
	for (int i = 0; i < states.size(); i++) {
		std::string stateId = ATTR(states[i], "id");
		NodeSet<std::string> transitions = filterChildElements(_nsInfo.xmlNSPrefix + "transition", states[i]);
		// some transitions are in the inital elements
		NodeSet<std::string> initials = filterChildElements(_nsInfo.xmlNSPrefix + "initial", states[i]);
		transitions.push_back(filterChildElements(_nsInfo.xmlNSPrefix + "transition", initials));
		for (int j = 0; j < transitions.size(); j++) {
			Element<std::string> transition = Element<std::string>(transitions[j]);
			transition.setAttribute("id", stateId + ":"+ toStr(j + 1));
		}
	}
}

void FlatteningInterpreter::beforeMicroStep(Interpreter interpreter) {
}
void FlatteningInterpreter::onStableConfiguration(Interpreter interpreter) {
}
void FlatteningInterpreter::beforeExitingState(Interpreter interpreter, const Arabica::DOM::Element<std::string>& state, bool moreComing) {
	GlobalTransition::Action action;
	action.exited = state;
	_currGlobalTransition->actions.push_back(action);
	_currGlobalTransition->exited.push_back(state);
}
void FlatteningInterpreter::beforeEnteringState(Interpreter interpreter, const Arabica::DOM::Element<std::string>& state, bool moreComing) {
	GlobalTransition::Action action;
	action.entered = state;
	_currGlobalTransition->actions.push_back(action);
	_currGlobalTransition->entered.push_back(state);
}
void FlatteningInterpreter::beforeTakingTransition(Interpreter interpreter, const Arabica::DOM::Element<std::string>& transition, bool moreComing) {
}


GlobalState::GlobalState(const Arabica::XPath::NodeSet<std::string>& activeStates_,
                         const Arabica::XPath::NodeSet<std::string>& alreadyEnteredStates_, // we need to remember for binding=late
                         const std::map<std::string, Arabica::XPath::NodeSet<std::string> >& historyStates_) {

	// make copies and sort
	activeStates = activeStates_;
	alreadyEnteredStates = alreadyEnteredStates_;
	historyStates = historyStates_;
	isFinal = true; // is set to false if we contain a non-final state

	// start state is not final
	if (activeStates.size() == 0) {
		isFinal = false;
	}

	// sort configuration
	activeStates.to_document_order();
	alreadyEnteredStates.to_document_order();
	for(std::map<std::string, Arabica::XPath::NodeSet<std::string> >::iterator historyIter = historyStates.begin();
	        historyIter != historyStates.end();
	        historyIter++) {
		historyIter->second.to_document_order();
	}

	// create a unique identifier for a global configuration
	std::ostringstream idSS;
	idSS << "active-";
	for (int i = 0; i < activeStates.size(); i++) {
		if (!Interpreter::isFinal(activeStates[i]))
			isFinal = false;
		idSS << ATTR(activeStates[i], "id") << "-";
	}
	idSS << ";";
	idSS << "entered-";
	for (int i = 0; i < alreadyEnteredStates.size(); i++) {
		idSS << ATTR(alreadyEnteredStates[i], "id") << "-";
	}
	idSS << ";";

	for(std::map<std::string, Arabica::XPath::NodeSet<std::string> >::const_iterator histIter = historyStates.begin();
	        histIter != historyStates.end();
	        histIter++) {
		const Arabica::XPath::NodeSet<std::string>& histStates = histIter->second;
		idSS << "history-";
		idSS << histIter->first << "-";
		for (int i = 0; i < histStates.size(); i++) {
			idSS << ATTR(histStates[i], "id") << "-";
		}
	}

	stateId = idSS.str();
}

GlobalTransition::GlobalTransition(const Arabica::XPath::NodeSet<std::string>& transitionSet, DataModel dataModel) {
	transitions = transitionSet;
	isValid = true;
	isEventless = true;

#if 0
	std::cout << "################" << std::endl;
	for (int i = 0; i < transitions.size(); i++) {
		std::cout << transitions[i] << std::endl;
	}
	std::cout << "################" << std::endl;
#endif

	std::list<std::string> conditions;
	std::ostringstream setId; // also build id for subset
	for (int i = 0; i < transitions.size(); i++) {
		// get a unique string for the transition - we assume it is sorted
		assert(HAS_ATTR(transitions[i], "id"));
		setId << ATTR(transitions[i], "id") << "-";

		// gather conditions while we are iterating anyway
		if (HAS_ATTR(transitions[i], "cond")) {
			conditions.push_back(ATTR(transitions[i], "cond"));
		}
	}
	transitionId = setId.str();

	/**
	 * Can these events event occur together? They can't if:
	 * 1. event / eventless is mixed
	 * 2. target / targetless is mixed (?)
	 * 3. there is no common prefix for their event attribute
	 */

	bool foundWithEvent = false;
	bool foundEventLess = false;
	bool foundWithTarget = false;
	bool foundTargetLess = false;

	for (int i = 0; i < transitions.size(); i++) {
		if (HAS_ATTR(transitions[i], "eventexpr")) {
			Event e("error.execution", Event::PLATFORM);
			e.data.compound["cause"] = "Cannot flatten document with eventexpr attributes";
			throw e;
		}
		if (HAS_ATTR(transitions[i], "event")) {
			foundWithEvent = true;
			if (foundEventLess)
				break;
		} else {
			foundEventLess = true;
			if (foundWithEvent)
				break;
		}
		if (HAS_ATTR(transitions[i], "target")) {
			foundWithTarget = true;
			if (foundTargetLess)
				break;
		} else {
			foundTargetLess = true;
			if (foundWithTarget)
				break;
		}

	}

	// do not mix eventless and event transitions
	if (foundEventLess && foundWithEvent) {
		isValid = false;
		return;
	}

	// 403c vs 229 / 403b - solved via filterChildEnabled
	if (foundTargetLess && foundWithTarget) {
//		isValid = false;
//		return;
	}

	isEventless = foundEventLess;
	isTargetless = !foundWithTarget;

	// is there a set of event names that would enable this conflict-free transition set?
	if (foundWithEvent) {
		// get the set of longest event descriptors that will enable this transition set
		eventNames = getCommonEvents(transitions);
		if (eventNames.size() == 0) {
//			LOG(INFO) << "No event will activate this conflict-free subset" << std::endl;
			isValid = false;
			return;
		} else {
			std::string seperator = "";
			for (std::list<std::string>::iterator eventIter = eventNames.begin();
			        eventIter != eventNames.end();
			        eventIter++) {
				eventDesc += seperator + *eventIter;
				seperator = " ";
			}
		}
		if (eventDesc.size() == 0)
			eventDesc = "*";
	}

	if (conditions.size() > 0) {
		condition = dataModel.andExpressions(conditions);
		if (condition.size() == 0) {
			LOG(ERROR) << "Datamodel does not support to conjungate expressions!" << std::endl;
		}
	}
}

std::list<std::string> GlobalTransition::getCommonEvents(const NodeSet<std::string>& transitions) {
	std::list<std::string> prefixes;
	std::list<std::string> longestPrefixes;

	for (int i = 0; i < transitions.size(); i++) {
		// for every transition
		std::list<std::string> eventNames = Interpreter::tokenizeIdRefs(ATTR(transitions[i], "event"));

		for (std::list<std::string>::iterator eventNameIter = eventNames.begin();
		        eventNameIter != eventNames.end();
		        eventNameIter++) {
			// for every event descriptor
			std::string eventName = *eventNameIter;

			// remove trailing .*
			if (eventName.find("*", eventName.size() - 1) != std::string::npos)
				eventName = eventName.substr(0, eventName.size() - 1);
			if (eventName.find(".", eventName.size() - 1) != std::string::npos)
				eventName = eventName.substr(0, eventName.size() - 1);

			bool isMatching = true;
			for (int j = 0; j < transitions.size(); j++) {
				// check if token would activate all other transitions
				if (i == j)
					continue;
				if (!Interpreter::nameMatch(ATTR(transitions[j], "event"), eventName)) {
					isMatching = false;
					break;
				}
			}
			if (isMatching) {
				prefixes.push_back(eventName);
			}
		}
	}

	// from the set of event names, remove those that are prefixes
	for (std::list<std::string>::iterator outerEventNameIter = prefixes.begin();
	        outerEventNameIter != prefixes.end();
	        outerEventNameIter++) {
		for (std::list<std::string>::iterator innerEventNameIter = prefixes.begin();
		        innerEventNameIter != prefixes.end();
		        innerEventNameIter++) {
			if (!iequals(*outerEventNameIter, *innerEventNameIter) && Interpreter::nameMatch(*outerEventNameIter, *innerEventNameIter)) {
				goto IS_PREFIX;
			}
		}
		longestPrefixes.push_back(*outerEventNameIter);
IS_PREFIX:
		;
	}
	return longestPrefixes;
}

}
