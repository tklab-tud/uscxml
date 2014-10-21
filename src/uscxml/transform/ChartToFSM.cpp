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
#include "uscxml/transform/FlatStateIdentifier.h"
#include "uscxml/Convenience.h"
#include "uscxml/Factory.h"

#include <DOM/io/Stream.hpp>
#include <glog/logging.h>

#include <iostream>
#include "uscxml/UUID.h"
#include <math.h>
#include <string.h>
#include <algorithm>
#undef max
#include <limits>

#define UNDECIDABLE 2147483647
#define MIN(X,Y) ((X) < (Y) ? (X) : (Y))

#define DUMP_STATS(nrTrans) \
uint64_t now = tthread::chrono::system_clock::now(); \
if (now - _lastTimeStamp > 1000) { \
	std::cerr << "T: " << _perfTransTotal << " [" << _perfTransProcessed << "/sec]"; \
	if (nrTrans > 0) { \
		std::cerr << " - 2**" << nrTrans << " = " << pow(2.0, static_cast<double>(nrTrans)); \
	} \
	std::cerr << std::endl; \
	std::cerr << "S: " << _globalConf.size() << " [" << _perfStatesProcessed << "/sec]" << std::endl; \
	std::cerr << "C: " << _perfStatesCachedTotal << " [" << _perfStatesCachedProcessed << "/sec]" << std::endl; \
	std::cerr << "X: " << _perfStatesSkippedTotal << " [" << _perfStatesSkippedProcessed << "/sec]" << std::endl; \
	std::cerr << _perfTransTotal << ", " << _perfTransProcessed << ", " << _globalConf.size() << ", " << _perfStatesProcessed << ", "; \
	std::cerr <<_perfStatesCachedTotal << ", " << _perfStatesCachedProcessed << ", " << _perfStatesSkippedTotal << ", " << _perfStatesSkippedProcessed << std::endl; \
	std::cerr << std::endl; \
	_perfTransProcessed = 0; \
	_perfStatesProcessed = 0; \
	_perfStatesCachedProcessed = 0; \
	_perfStatesSkippedProcessed = 0; \
	_lastTimeStamp = now; \
}


#define DUMP_TRANSSET(where) \
{\
std::cout << std::endl;\
std::cout << "** " << transitions.size() << " ** " << where << std::endl;\
	for (int m = 0; m < transitions.size(); m++) {\
		std::cout << transitions[m] << std::endl;\
	}\
}

namespace uscxml {


using namespace Arabica::DOM;
using namespace Arabica::XPath;


#define DETAIL_EXEC_CONTENT(field, actPtr) \
std::cerr << " " << #field << " / " << TAGNAME_CAST(actPtr->field) << " ("; \
NodeSet<std::string> contents = filterChildType(Node_base::ELEMENT_NODE, actPtr->field, true); \
for (int i = 0; i < contents.size(); i++) { \
	std::cerr << " " << TAGNAME_CAST(contents[i]); \
} \
std::cerr << ")";


uint64_t Complexity::stateMachineComplexity(const Arabica::DOM::Element<std::string>& root) {
	Complexity complexity = calculateStateMachineComplexity(root);
	uint64_t value = complexity.value;
	for (std::list<uint64_t>::const_iterator histIter = complexity.history.begin(); histIter != complexity.history.end(); histIter++) {
		value *= *histIter;
	}

	return value;
}

Complexity Complexity::calculateStateMachineComplexity(const Arabica::DOM::Element<std::string>& root) {
	Complexity complexity;

	bool hasFlatHistory = false;
	bool hasDeepHistory = false;

	Arabica::DOM::NodeList<std::string> childElems = root.getChildNodes();
	for (int i = 0; i < childElems.getLength(); i++) {
		if (childElems.item(i).getNodeType() != Node_base::ELEMENT_NODE)
			continue;
		Element<std::string> childElem = Element<std::string>(childElems.item(i));
		if (InterpreterImpl::isHistory(childElem)) {
			if (HAS_ATTR(childElem, "type") && ATTR(childElem, "type") == "deep") {
				hasDeepHistory = true;
			} else {
				hasFlatHistory = true;
			}
		}
	}

	if (InterpreterImpl::isCompound(root) || TAGNAME(root) == "scxml") {
		// compounds can be in any of the child state -> add
		NodeSet<std::string> childs = InterpreterImpl::getChildStates(root);
		for (int i = 0; i < childs.size(); i++) {
			complexity += calculateStateMachineComplexity(Element<std::string>(childs[i]));
		}
		if (hasFlatHistory) {
			complexity.history.push_back(childs.size());
		}
		if (hasDeepHistory) {
			complexity.history.push_back(complexity.value);
		}
	} else if (InterpreterImpl::isParallel(root)) {
		// parallels are in all states -> multiply
		NodeSet<std::string> childs = InterpreterImpl::getChildStates(root);
		complexity.value = 1;
		for (int i = 0; i < childs.size(); i++) {
			complexity *= calculateStateMachineComplexity(Element<std::string>(childs[i]));
		}
		if (hasDeepHistory) {
			complexity.history.push_back(complexity.value);
		}

	} else if (InterpreterImpl::isAtomic(root)) {
		return 1;
	}

	return complexity;
}


ChartToFSM::ChartToFSM(const Interpreter& other) {

	cloneFrom(other.getImpl());
	
	_lastTimeStamp = tthread::chrono::system_clock::now();
	_perfTransProcessed = 0;
	_perfTransTotal = 0;
	_perfStatesProcessed = 0;
	_perfStatesSkippedProcessed = 0;
	_perfStatesSkippedTotal = 0;
	_perfStatesCachedProcessed = 0;
	_perfStatesCachedTotal = 0;
	
	_start = NULL;
	_currGlobalTransition = NULL;
	_lastTransientStateId = 0;

	_lastStateIndex = 0;
	_lastTransIndex = 0;
	
	_maxEventSentChain = 0;
	_maxEventRaisedChain = 0;
	_doneEventRaiseTolerance = 0;
	
	// create a _flatDoc for the FSM
	DOMImplementation<std::string> domFactory = Arabica::SimpleDOM::DOMImplementation<std::string>::getDOMImplementation();
	_flatDoc = domFactory.createDocument(other.getDocument().getNamespaceURI(), "", 0);

	addMonitor(this);
}

ChartToFSM::~ChartToFSM() {
	std::map<std::string, GlobalState*>::iterator confIter = _globalConf.begin();
	while(confIter != _globalConf.end()) {
		std::list<GlobalTransition*>::iterator transIter = confIter->second->sortedOutgoing.begin();
		while (transIter != confIter->second->sortedOutgoing.end()) {
			delete *transIter;
			transIter++;
		}
		delete confIter->second;
		confIter++;
	}
	
	// tear down caches
	Arabica::XPath::NodeSet<std::string> allTransitions = filterChildElements(_nsInfo.xmlNSPrefix + "transition", _scxml, true);
	for (int i = 0; i < allTransitions.size(); i++) {
		_transParents.erase(allTransitions[i]);
	}

}

Document<std::string> ChartToFSM::getDocument() const {
	return _flatDoc;
}

InterpreterState ChartToFSM::interpret() {

	init();
	setupIOProcessors();

	uint64_t complexity = Complexity::stateMachineComplexity(_scxml) + 1;
	std::cerr << "Approximate Complexity: " << complexity << std::endl;

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

	// setup caches
	{
		Arabica::XPath::NodeSet<std::string> allTransitions = filterChildElements(_nsInfo.xmlNSPrefix + "transition", _scxml, true);
		indexedTransitions.reserve(allTransitions.size());
		for (int i = 0; i < allTransitions.size(); i++) {
			_transParents[allTransitions[i]] = InterpreterImpl::getParentState(allTransitions[i]);
		}
	}

	
	_binding = (HAS_ATTR(_scxml, "binding") && iequals(ATTR(_scxml, "binding"), "late") ? LATE : EARLY);

	// set invokeid for all invokers to parent state if none given
	NodeSet<std::string> invokers = filterChildElements(_nsInfo.xmlNSPrefix + "invoke", _scxml, true);
	for (int i = 0; i < invokers.size(); i++) {
		Element<std::string> invokerElem = Element<std::string>(invokers[i]);
		invokerElem.setAttribute("parent", ATTR_CAST(invokerElem.getParentNode(), "id"));
	}
	// reset
	_globalConf.clear();
	_currGlobalTransition = NULL;

	// very first state
	_start = new GlobalState(_configuration, _alreadyEntered, _historyValue, _nsInfo.xmlNSPrefix, this);
	_globalConf[_start->stateId] = _start;
	_globalConf[_start->stateId]->index = _lastStateIndex++;

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
		transitionElem.setAttribute("target", ATTR_CAST(initialStates[i], "id"));
		initialElem.appendChild(transitionElem);
		_scxml.appendChild(initialElem);
		initialTransitions.push_back(transitionElem);
	}
	
	annotateRaiseAndSend(_scxml);
	
//	std::cout << _scxml << std::endl;
	
	indexTransitions(_scxml);

	// reverse indices for most prior to be in front
	std::reverse(indexedTransitions.begin(), indexedTransitions.end());
	
	// add initial transitions as least prior
	for (int i = 0; i < initialTransitions.size() ; i++) {
		indexedTransitions.push_back(Element<std::string>(initialTransitions[i]));
	}

	// set index attribute for transitions
	for (int i = 0; i < indexedTransitions.size(); i++) {
		indexedTransitions[i].setAttribute("index", toStr(i));
	}

//	int lastTransIndex = indexedTransitions.size();
//	for (int i = 0; i < initialTransitions.size() ; i++, lastTransIndex++) {
//		indexedTransitions[i].setAttribute("index", toStr(indexedTransitions.size() - 1 - i));
//	}

	// gather and set index attribute o states
	NodeSet<std::string> allStates = getAllStates();
	allStates.to_document_order();
	
	indexedStates.resize(allStates.size());
	for (int i = 0; i < allStates.size(); i++) {
		Element<std::string> state = Element<std::string>(allStates[i]);

		// while we are iterating, determine deepest nested level
		size_t nrAncs = getProperAncestors(state, _scxml).size();
		if (_doneEventRaiseTolerance < nrAncs)
			_doneEventRaiseTolerance  = nrAncs;

		state.setAttribute("index", toStr(i));
		indexedStates[i] = state;
	}

//	std::cerr << _scxml << std::endl;

	GlobalTransition* globalTransition = new GlobalTransition(initialTransitions, _dataModel, this);
	globalTransition->index = _lastTransIndex++;

	_start->sortedOutgoing.push_back(globalTransition);
	globalTransition->source = _start->stateId;
	_currGlobalTransition = globalTransition;

	enterStates(initialTransitions);
	globalTransition->destination = FlatStateIdentifier::toStateId(_configuration);
	
	explode();

#if 0
	// print set of global configurations
	for(std::map<std::string, GlobalState*>::iterator globalConfIter = _globalConf.begin();
	        globalConfIter != _globalConf.end();
	        globalConfIter++) {
		std::cerr << globalConfIter->first << std::endl;
	}
	std::cerr << _globalConf.size() << std::endl;
#endif

	std::cerr << "Actual Complexity: " << _globalConf.size() << std::endl;
	std::cerr << "Internal Queue: " << _maxEventRaisedChain << std::endl;
	std::cerr << "External Queue: " << _maxEventSentChain << std::endl;
	return _state;
}

void ChartToFSM::executeContent(const Arabica::DOM::Element<std::string>& content, bool rethrow) {
//	std::cerr << content << std::endl;
//	std::cerr << TAGNAME(content) << std::endl;

	GlobalTransition::Action action;

	if (false) {
	} else if (TAGNAME(content) == "transition" && content.hasChildNodes()) {
		action.transition = content;
	} else if (TAGNAME(content) == "onexit") {
		action.onExit = content;
	} else if (TAGNAME(content) == "onentry") {
		action.onEntry = content;
	} else if (TAGNAME(content) == "history") {
		assert(false);
	} else { // e.g. global script elements
		return;
	}
	assert(content.hasAttribute("raise") && content.hasAttribute("send"));

	std::string raiseAttr = content.getAttribute("raise");
	std::string sendAttr = content.getAttribute("send");
	
	_currGlobalTransition->eventsRaised = (raiseAttr == "-1" ? UNDECIDABLE : _currGlobalTransition->eventsRaised + strTo<uint32_t>(raiseAttr));
	_currGlobalTransition->eventsSent = (sendAttr == "-1" ? UNDECIDABLE : _currGlobalTransition->eventsSent + strTo<uint32_t>(sendAttr));
	
	if (_currGlobalTransition->eventsRaised > _maxEventRaisedChain)
		_maxEventRaisedChain = _currGlobalTransition->eventsRaised;
	if (_currGlobalTransition->eventsSent > _maxEventSentChain)
		_maxEventSentChain = _currGlobalTransition->eventsSent;

	_currGlobalTransition->actions.push_back(action);
	_currGlobalTransition->hasExecutableContent = true;
}

void ChartToFSM::invoke(const Arabica::DOM::Element<std::string>& element) {
	GlobalTransition::Action action;
	action.invoke = element;
	_currGlobalTransition->actions.push_back(action);
	_currGlobalTransition->hasExecutableContent = true;
}

void ChartToFSM::cancelInvoke(const Arabica::DOM::Element<std::string>& element) {
	GlobalTransition::Action action;
	action.uninvoke = element;
	_currGlobalTransition->actions.push_back(action);
	_currGlobalTransition->hasExecutableContent = true;
}

void ChartToFSM::internalDoneSend(const Arabica::DOM::Element<std::string>& state) {
	if (!isState(state))
		return;

	if (parentIsScxmlState(state))
		return;

//	std::cerr << "internalDoneSend: " << state << std::endl;

	// create onentry with a raise element
	Element<std::string> onentry = _flatDoc.createElementNS(_nsInfo.nsURL, "onentry");
	_nsInfo.setPrefix(onentry);

	Element<std::string> raise = _flatDoc.createElementNS(_nsInfo.nsURL, "raise");
	_nsInfo.setPrefix(raise);

	onentry.appendChild(raise);

	Arabica::XPath::NodeSet<std::string> doneDatas = filterChildElements(_nsInfo.xmlNSPrefix + "donedata", state);
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

	raise.setAttribute("event", "done.state." + ATTR_CAST(state.getParentNode(), "id")); // parent?!

	GlobalTransition::Action action;
	action.onEntry = onentry;

	_currGlobalTransition->actions.push_back(action);
	_currGlobalTransition->eventsRaised++;
	_currGlobalTransition->hasExecutableContent = true;

}

static bool isSuperset(const GlobalTransition* t1, const GlobalTransition* t2) {
	bool isSuperset = true;

	if (t1->transitionRefs.size() >= t2->transitionRefs.size())
		return false;

	NodeSet<std::string> t1Trans = t1->getTransitions();
	NodeSet<std::string> t2Trans = t2->getTransitions();
	
	for (int i = 0; i < t1Trans.size(); i++) {
		if (!InterpreterImpl::isMember(t1Trans[i], t2Trans)) {
			isSuperset = false;
		}
	}
	return isSuperset;
}

// return false if two transitions have the same source
std::map<Arabica::DOM::Node<std::string>, Arabica::DOM::Node<std::string> > ChartToFSM::_transParents;
bool ChartToFSM::filterSameState(const NodeSet<std::string>& transitions) {

	for (unsigned int i = 0; i < transitions.size(); i++) {
		Node<std::string> p1 = _transParents[transitions[i]];

		for (unsigned int j = i + 1; j < transitions.size(); j++) {
//			if (i == j)
//				continue;
			Node<std::string> p2 = _transParents[transitions[j]];

			if (p1 == p2)
				return false;
		}
	}
	return true;
}

static bool filterChildEnabled(const NodeSet<std::string>& transitions) {
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
			p2 = p2.getParentNode(); // TODO: think about again!
			while(p2) {
				if (p1 == p2) {
					std::string eventDesc1 = ATTR_CAST(t1, "event");
					std::string eventDesc2 = ATTR_CAST(t2, "event");
					if (InterpreterImpl::nameMatch(eventDesc1, eventDesc2)) {
						return false;
					}
				}
				p2 = p2.getParentNode();
			}
		}
		filteredTransitions.push_back(t1);
		;
	}
	return true;
}

bool ChartToFSM::hasForeachInBetween(const Arabica::DOM::Node<std::string>& ancestor, const Arabica::DOM::Node<std::string>& child) {
	if (!ancestor || !child)
		return false;
	
	Node<std::string> currChild = child;
	while(currChild != ancestor) {
		if (!currChild.getParentNode())
			return false;
		if (TAGNAME_CAST(currChild) == "foreach")
			return true;
		currChild = currChild.getParentNode();
	}
	return false;
}

void ChartToFSM::annotateRaiseAndSend(const Arabica::DOM::Element<std::string>& root) {
	NodeSet<std::string> execContent;
	execContent.push_back(filterChildElements(_nsInfo.xmlNSPrefix + "transition", _scxml, true));
	execContent.push_back(filterChildElements(_nsInfo.xmlNSPrefix + "onentry", _scxml, true));
	execContent.push_back(filterChildElements(_nsInfo.xmlNSPrefix + "onexit", _scxml, true));
	for (int i = 0; i < execContent.size(); i++) {
		Element<std::string> execContentElem(execContent[i]);

		int nrRaise = 0;
		NodeSet<std::string> raise = filterChildElements(_nsInfo.xmlNSPrefix + "raise", execContent[i], true);
		for (int j = 0; j < raise.size(); j++) {
			if (hasForeachInBetween(execContent[i], raise[j])) {
				execContentElem.setAttribute("raise", "-1");
				goto DONE_COUNT_RAISE;
			} else {
				nrRaise++;
			}
		}
		execContentElem.setAttribute("raise", toStr(nrRaise));

	DONE_COUNT_RAISE:
		
		int nrSend = 0;
		NodeSet<std::string> sends = filterChildElements(_nsInfo.xmlNSPrefix + "send", execContent[i], true);
		for (int j = 0; j < sends.size(); j++) {
			if (hasForeachInBetween(execContent[i], sends[j])) {
				execContentElem.setAttribute("send", "-1");
				goto DONE_COUNT_SEND;
			} else {
				nrSend++;
			}
		}
		execContentElem.setAttribute("send", toStr(nrSend));

	DONE_COUNT_SEND:
		;
	}
}

void ChartToFSM::indexTransitions(const Arabica::DOM::Element<std::string>& root) {
	// breadth first traversal of transitions
	Arabica::XPath::NodeSet<std::string> levelTransitions = filterChildElements(_nsInfo.xmlNSPrefix + "transition", root);
	for (int i = levelTransitions.size() - 1; i >= 0; i--) {
		// push into index starting with least prior
		indexedTransitions.push_back(Element<std::string>(levelTransitions[i]));
	}

	Arabica::XPath::NodeSet<std::string> nextLevel = filterChildType(Arabica::DOM::Node_base::ELEMENT_NODE, root);
	for (int i = nextLevel.size() - 1; i >= 0; i--) {
		Element<std::string> stateElem = Element<std::string>(nextLevel[i]);
		if (isState(stateElem))
			indexTransitions(stateElem);
	}
}

bool GlobalTransition::operator< (const GlobalTransition& other) const {
	const std::vector<Arabica::DOM::Element<std::string> >& indexedTransitions = interpreter->indexedTransitions;
	NodeSet<std::string> transitions = getTransitions();
	
	for (std::vector<Element<std::string> >::const_iterator transIter = indexedTransitions.begin(); transIter != indexedTransitions.end(); transIter++) {
		const Element<std::string>& refTrans = *transIter;
		NodeSet<std::string> otherTransitions = other.getTransitions();

		if (InterpreterImpl::isMember(refTrans, transitions) && !InterpreterImpl::isMember(refTrans, otherTransitions)) {
			return true;
		}
		if (!InterpreterImpl::isMember(refTrans, transitions) && InterpreterImpl::isMember(refTrans, otherTransitions)) {
			return false;
		}
	}
	return true; // actually, they are equal
}

template <typename T> bool PtrComp(const T * const & a, const T * const & b) {
	return *a < *b;
}


/**
 * subset only removes transitions without cond -> superset will always be enabled
 */
bool hasUnconditionalSuperset (GlobalTransition* first, GlobalTransition* second) {

	NodeSet<std::string> firstTransitions = first->getTransitions();
	NodeSet<std::string> secondTransitions = first->getTransitions();
	
	if (isSuperset(second, first)) {
		for (int i = 0; i < firstTransitions.size(); i++) {
			if (!InterpreterImpl::isMember(firstTransitions[i], secondTransitions)) {
				if (HAS_ATTR_CAST(firstTransitions[i], "cond")) {
					return false; // second can't be removed
				}
			}
		}
		return true; // remove second
	}
	return false; //second can't be removed
}

bool hasEarlierUnconditionalMatch(GlobalTransition* first, GlobalTransition* second) {
	if (first->eventDesc == second->eventDesc) {
		if (first->condition.size() == 0)
			return true;
	}
	return false;
}

// for some reason, unique is not quite up to the task
std::list<GlobalTransition*> reapplyUniquePredicates(std::list<GlobalTransition*> list) {
	
	for (std::list<GlobalTransition*>::iterator outerIter = list.begin();
			 outerIter != list.end();
			 outerIter++) {
		for (std::list<GlobalTransition*>::iterator innerIter = outerIter;
				 innerIter != list.end();
				 innerIter++) {
			
			if (innerIter == outerIter)
				continue;
			
			GlobalTransition* t1 = *outerIter;
			GlobalTransition* t2 = *innerIter;
			
			if (hasUnconditionalSuperset(t1, t2)) {
				list.erase(outerIter++);
				continue;
			} else if (hasUnconditionalSuperset(t2, t1)) {
				list.erase(innerIter++);
				continue;
			}
			if (hasEarlierUnconditionalMatch(t1, t2)) {
				list.erase(innerIter++);
				continue;
			}
		}
	}
	
	return list;
}

void ChartToFSM::getPotentialTransitionsForConf(const Arabica::XPath::NodeSet<std::string>& conf, std::map<std::string, GlobalTransition*>& outMap) {
	// get all transition elements from states in the current configuration
	NodeSet<std::string> allTransitions = filterChildElements(_nsInfo.xmlNSPrefix + "transition", conf);
	
	if (allTransitions.size() == 0)
		return; // no transitions
	
	int nrElements = allTransitions.size();
	int k = 0;
	int* stack = (int*)malloc((nrElements + 1) * sizeof(int));
	memset(stack, 0, (nrElements + 1) * sizeof(int));
	
	while(1) {
		// create the power set of all potential transitions - this is expensive!
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
		//		std::cerr << globalState->stateId << " [" << nrElements << "]: " << std::endl;
		for (int i = 1; i <= k; i++) {
			//			std::cerr << stack[i] - 1 << ", ";
			transitions.push_back(allTransitions[stack[i] - 1]);
		}
		//		std::cerr << std::endl;
		
		//		transitions.push_back(allTransitions[0]);
		//		transitions.push_back(allTransitions[4]);
		//		transitions.push_back(allTransitions[5]);
		//		transitions.push_back(allTransitions[7]);
		
		bool dump = false;
		
		//		if (k == 4 && stack[1] == 1 && stack[2] == 5 && stack[3] == 6 && stack[4] == 8) {
		//			dump = true;
		//		}
		
		if (dump) DUMP_TRANSSET("at start");
		
		_perfTransTotal++;
		_perfTransProcessed++;
		
		DUMP_STATS(nrElements);
		
		// remove transitions in the same state
		if(!filterSameState(transitions))
			continue;
		if (dump) DUMP_TRANSSET("after same state filtered");
		
		// remove those transitions with a child transition
		if(!filterChildEnabled(transitions))
			continue;
		if (dump) DUMP_TRANSSET("after child enabled filtered");
		
		// reduce to conflict-free subset
		// transitions.to_document_order();
		transitions = removeConflictingTransitions(transitions);
		if (dump) DUMP_TRANSSET("after conflicting filtered");
		
		// algorithm can never reduce to empty set
		assert(transitions.size() > 0);
		
		// create a GlobalTransition object from the set
		GlobalTransition* transition = new GlobalTransition(transitions, _dataModel, this);
		if (!transition->isValid) {
			// this set of transitions can not be enabled together
			delete transition;
			continue;
		}
		transition->index = _lastTransIndex++;

		// two combinations might have projected onto the same conflict-free set
		if (outMap.find(transition->transitionId) != outMap.end()) {
			//			std::cerr << "skipping as projected onto existing conflict-free subset" << std::endl;
			delete transition;
			continue;
		}
		
		// remember this conflict-free set
		//		std::cerr << "New conflict-free subset: " << transition->transitionId << ":" << transition->eventDesc << std::endl;
		outMap[transition->transitionId] = transition;
	}
	return;
}
	
void ChartToFSM::explode() {

	std::list<std::pair<GlobalTransition*, GlobalState*> > statesRemaining;
	statesRemaining.push_back(std::make_pair(_currGlobalTransition, new GlobalState(_configuration, _alreadyEntered, _historyValue, _nsInfo.xmlNSPrefix, this)));
	
	// add all invokers for initial transition
	for (unsigned int i = 0; i < _statesToInvoke.size(); i++) {
		NodeSet<std::string> invokes = filterChildElements(_nsInfo.xmlNSPrefix + "invoke", _statesToInvoke[i]);
		for (unsigned int j = 0; j < invokes.size(); j++) {
			invoke(Element<std::string>(invokes[j]));
		}
	}
	_statesToInvoke = NodeSet<std::string>();

	/**
	 We need this to be a recursion in order not to exhaust the stack
	 */
	
	// append new global states and pop from front
	while(statesRemaining.size() > 0) {
		DUMP_STATS(0);
		
		GlobalState* globalState = statesRemaining.front().second;
		_currGlobalTransition = statesRemaining.front().first;
		statesRemaining.pop_front();
		
		// used to be conditionalized, we will just assume
		assert(_currGlobalTransition);

		if (_globalConf.find(globalState->stateId) != _globalConf.end()) {
			if (_currGlobalTransition->isEventless) {
				// we arrived via a spontaneaous transition, do we need to update?
				updateRaisedAndSendChains(_globalConf[globalState->stateId], _currGlobalTransition, std::set<GlobalTransition*>());
			}
			delete globalState;
			_perfStatesSkippedTotal++;
			_perfStatesSkippedProcessed++;
			continue; // we have already been here
		}

		_perfStatesProcessed++;

		_configuration = globalState->getActiveStates();
		_alreadyEntered = globalState->getAlreadyEnteredStates();
		_historyValue = globalState->getHistoryStates();

		// remember as global configuration
		_globalConf[globalState->stateId] = globalState;
		_globalConf[globalState->stateId]->index = _lastStateIndex++;
		
		if(_globalConf[globalState->stateId]->isFinal)
			continue; // done in this branch

		if (_transPerActiveConf.find(globalState->activeId) != _transPerActiveConf.end()) {
			// we already know these transition sets, just copy over
			std::list<GlobalTransition*>::iterator sortTransIter = _transPerActiveConf[globalState->activeId]->sortedOutgoing.begin();
			while(sortTransIter != _transPerActiveConf[globalState->activeId]->sortedOutgoing.end()) {
				globalState->sortedOutgoing.push_back(new GlobalTransition(**sortTransIter)); // copy constructor
				globalState->sortedOutgoing.back()->index = _lastTransIndex++;
				sortTransIter++;
			}
			_perfStatesCachedTotal++;
			_perfStatesCachedProcessed++;

		} else {
			// we need to calculate the potential optimal transition sets
			std::map<std::string, GlobalTransition*> transitionSets;
			getPotentialTransitionsForConf(refsToStates(globalState->activeStatesRefs), transitionSets);

			// TODO: reduce and sort transition sets
			for(std::map<std::string, GlobalTransition*>::iterator transSetIter = transitionSets.begin();
					transSetIter != transitionSets.end();
					transSetIter++) {
				globalState->sortedOutgoing.push_back(transSetIter->second);
			}
			
			globalState->sortedOutgoing.sort(PtrComp<GlobalTransition>);
			globalState->sortedOutgoing.unique(hasUnconditionalSuperset);
			globalState->sortedOutgoing.unique(hasEarlierUnconditionalMatch);
			// unique is not quite like what we need, but it was a start
			globalState->sortedOutgoing = reapplyUniquePredicates(globalState->sortedOutgoing);
			
			_transPerActiveConf[globalState->activeId] = globalState;
		}
		
		// take every transition set and append resulting new state
		for(std::list<GlobalTransition*>::iterator transIter = globalState->sortedOutgoing.begin();
				transIter != globalState->sortedOutgoing.end();
				transIter++) {
			
			GlobalTransition* incomingTrans = _currGlobalTransition;
			GlobalTransition* outgoingTrans = *transIter;
			
			outgoingTrans->source = globalState->stateId;
			_currGlobalTransition = outgoingTrans;

			microstep(refsToTransitions(outgoingTrans->transitionRefs));

			// if outgoing transition is spontaneous, add number of events to chain
			if (outgoingTrans->isEventless) {
				outgoingTrans->eventsChainRaised = MIN(incomingTrans->eventsChainRaised + outgoingTrans->eventsRaised, UNDECIDABLE);
				outgoingTrans->eventsChainSent = MIN(incomingTrans->eventsChainSent + outgoingTrans->eventsSent, UNDECIDABLE);

				if (outgoingTrans->eventsChainRaised > _maxEventRaisedChain)
					_maxEventRaisedChain = outgoingTrans->eventsChainRaised;
				if (outgoingTrans->eventsChainSent > _maxEventSentChain)
					_maxEventSentChain = outgoingTrans->eventsChainSent;

			}

			statesRemaining.push_back(std::make_pair(outgoingTrans, new GlobalState(_configuration, _alreadyEntered, _historyValue, _nsInfo.xmlNSPrefix, this)));
			
			// add all invokers
			for (unsigned int i = 0; i < _statesToInvoke.size(); i++) {
				NodeSet<std::string> invokes = filterChildElements(_nsInfo.xmlNSPrefix + "invoke", _statesToInvoke[i]);
				for (unsigned int j = 0; j < invokes.size(); j++) {
					invoke(Element<std::string>(invokes[j]));
				}
			}
			_statesToInvoke = NodeSet<std::string>();

			// remember that the last transition lead here
			outgoingTrans->destination = statesRemaining.back().second->stateId;

			// reset state for next transition set
			_configuration = globalState->getActiveStates();
			_alreadyEntered = globalState->getAlreadyEnteredStates();
			_historyValue = globalState->getHistoryStates();
		}
	}

}

void ChartToFSM::updateRaisedAndSendChains(GlobalState* state, GlobalTransition* source, std::set<GlobalTransition*> visited) {
	for (std::list<GlobalTransition*>::iterator transIter = state->sortedOutgoing.begin(); transIter != state->sortedOutgoing.end(); transIter++) {
		GlobalTransition* transition = *transIter;
		
		if (!transition->isEventless)
			continue; // we do not care for eventful transitions
		
		// source leads to spontaneous transition -> update event chains
		bool eventChainsNeedUpdated = false;
		
		if (visited.find(transition) != visited.end()) {
			// potential spontaneous transition cycle!
			if (transition->eventsChainRaised > 0)
				_maxEventRaisedChain = UNDECIDABLE;
			if (transition->eventsChainSent > 0)
				_maxEventSentChain = UNDECIDABLE;
			return;
		}
		
		// UNDECIDABLE means "undecidable / endless"
		
		// will source increase our event chain?
		if (transition->eventsChainRaised != UNDECIDABLE &&
				transition->eventsChainRaised < source->eventsChainRaised + transition->eventsRaised) {
			// taking transition after source causes more events in chain
			transition->eventsChainRaised = MIN(source->eventsChainRaised + transition->eventsRaised, UNDECIDABLE);
			eventChainsNeedUpdated = true;
		}
		if (transition->eventsChainSent != UNDECIDABLE &&
				transition->eventsChainSent < source->eventsChainSent + transition->eventsSent) {
			// taking transition after source causes more events in chain
			transition->eventsChainSent = MIN(source->eventsChainSent + transition->eventsSent, UNDECIDABLE);
			eventChainsNeedUpdated = true;
		}

		if (eventChainsNeedUpdated &&
				transition->destination.length() > 0 &&
				_globalConf.find(transition->destination) != _globalConf.end()) {

			visited.insert(transition);
			// iterate all spontaneous transitions in destination and update event chains
			updateRaisedAndSendChains(_globalConf[transition->destination], transition, visited);
		}
		
		if (transition->eventsChainRaised > _maxEventRaisedChain)
			_maxEventRaisedChain = transition->eventsChainRaised;
		if (transition->eventsChainSent > _maxEventSentChain)
			_maxEventSentChain = transition->eventsChainSent;
	}
}

uint32_t ChartToFSM::getMinInternalQueueLength(uint32_t defaultVal) {
	if (_maxEventRaisedChain != UNDECIDABLE)
		return _maxEventRaisedChain + _doneEventRaiseTolerance;
	return defaultVal;
}

uint32_t ChartToFSM::getMinExternalQueueLength(uint32_t defaultVal) {
	if (_maxEventSentChain != UNDECIDABLE)
		return _maxEventSentChain;
	return defaultVal;
}

Arabica::XPath::NodeSet<std::string> ChartToFSM::refsToStates(const std::set<int>& stateRefs) {
	NodeSet<std::string> states;
	for (std::set<int>::const_iterator stateIter = stateRefs.begin(); stateIter != stateRefs.end(); stateIter++) {
		states.push_back(indexedStates[*stateIter]);
	}
	return states;
}

Arabica::XPath::NodeSet<std::string> ChartToFSM::refsToTransitions(const std::set<int>& transRefs) {
	NodeSet<std::string> transitions;
	for (std::set<int>::const_iterator transIter = transRefs.begin(); transIter != transRefs.end(); transIter++) {
		transitions.push_back(indexedTransitions[*transIter]);
	}
	return transitions;
}

#if 0
void ChartToFSM::labelTransitions() {
	// put a unique id on each transition
	Arabica::XPath::NodeSet<std::string> states = getAllStates();
	states.push_back(_scxml);
	for (int i = 0; i < states.size(); i++) {
		Arabica::DOM::Element<std::string> stateElem = Arabica::DOM::Element<std::string>(states[i]);
		std::string stateId = ATTR(stateElem, "id");
		NodeSet<std::string> transitions = filterChildElements(_nsInfo.xmlNSPrefix + "transition", stateElem);
		// some transitions are in the inital elements
		NodeSet<std::string> initials = filterChildElements(_nsInfo.xmlNSPrefix + "initial", stateElem);
		transitions.push_back(filterChildElements(_nsInfo.xmlNSPrefix + "transition", initials));
		for (int j = 0; j < transitions.size(); j++) {
			Element<std::string> transition = Element<std::string>(transitions[j]);
			transition.setAttribute("id", stateId + ":"+ toStr(j + 1));
		}
	}
}
#endif
	
void ChartToFSM::beforeMicroStep(Interpreter interpreter) {
}
void ChartToFSM::onStableConfiguration(Interpreter interpreter) {
}
void ChartToFSM::beforeExitingState(Interpreter interpreter, const Arabica::DOM::Element<std::string>& state, bool moreComing) {
	GlobalTransition::Action action;
	action.exited = state;
	_currGlobalTransition->actions.push_back(action);
}
void ChartToFSM::beforeEnteringState(Interpreter interpreter, const Arabica::DOM::Element<std::string>& state, bool moreComing) {
	GlobalTransition::Action action;
	action.entered = state;
	_currGlobalTransition->actions.push_back(action);
}
void ChartToFSM::beforeTakingTransition(Interpreter interpreter, const Arabica::DOM::Element<std::string>& transition, bool moreComing) {
}

GlobalState::GlobalState(const Arabica::XPath::NodeSet<std::string>& activeStates_,
                         const Arabica::XPath::NodeSet<std::string>& alreadyEnteredStates_, // we need to remember for binding=late
                         const std::map<std::string, Arabica::XPath::NodeSet<std::string> >& historyStates_,
                         const std::string& xmlNSPrefix,
												 ChartToFSM* flattener) {
	interpreter = flattener;
	
	// take references
	for (int i = 0; i < activeStates_.size(); i++) {
		activeStatesRefs.insert(strTo<int>(ATTR_CAST(activeStates_[i], "index")));
	}

	for (int i = 0; i < alreadyEnteredStates_.size(); i++) {
		alreadyEnteredStatesRefs.insert(strTo<int>(ATTR_CAST(alreadyEnteredStates_[i], "index")));
	}

	for (std::map<std::string, Arabica::XPath::NodeSet<std::string> >::const_iterator histIter = historyStates_.begin(); histIter != historyStates_.end(); histIter++) {
		for (int i = 0; i < histIter->second.size(); i++) {
			historyStatesRefs[histIter->first].insert(strTo<int>(ATTR_CAST(histIter->second[i], "index")));
		}
	}

	isFinal = false;

	// is state this final?
	for(int i = 0; i < activeStates_.size(); i++) {
		Arabica::DOM::Element<std::string> state = Arabica::DOM::Element<std::string>(activeStates_[i]);
		Arabica::DOM::Element<std::string> parentElem = (Arabica::DOM::Element<std::string>)state.getParentNode();
		if(InterpreterImpl::isFinal(state) && iequals(parentElem.getTagName(), xmlNSPrefix + "scxml")) {
			isFinal = true;
			break;
		}
	}

	FlatStateIdentifier flatStateId(getActiveStates(), getAlreadyEnteredStates(), getHistoryStates());
	stateId = flatStateId.getStateId();
	activeId = flatStateId.getFlatActive();
}

GlobalTransition::GlobalTransition(const Arabica::XPath::NodeSet<std::string>& transitionSet, DataModel dataModel, ChartToFSM* flattener) {
	interpreter = flattener;
	
	eventsRaised = 0;
	eventsSent = 0;
	eventsChainRaised = 0;
	eventsChainSent = 0;
	
	for (int i = 0; i < transitionSet.size(); i++) {
		transitionRefs.insert(strTo<int>(ATTR_CAST(transitionSet[i], "index")));
	}

	std::ostringstream setId; // also build id for subset
	std::string seperator = "";
	for (std::set<int>::iterator transIter = transitionRefs.begin(); transIter != transitionRefs.end(); transIter++) {
		setId << seperator << *transIter;
		seperator = "-";
	}
	transitionId = setId.str();

	hasExecutableContent = false;
	isValid = true;
	isEventless = true;
	
#if 0
	std::cerr << "################" << std::endl;
	for (int i = 0; i < transitions.size(); i++) {
		std::cerr << transitions[i] << std::endl;
	}
	std::cerr << "################" << std::endl;
#endif

	// first establish whether this is a valid set

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

	for (int i = 0; i < transitionSet.size(); i++) {
		Arabica::DOM::Element<std::string> transElem = Arabica::DOM::Element<std::string>(transitionSet[i]);
		if (HAS_ATTR(transElem, "eventexpr")) {
			ERROR_EXECUTION_THROW("Cannot flatten document with eventexpr attributes");
		}
		if (HAS_ATTR(transElem, "event")) {
			foundWithEvent = true;
			if (foundEventLess)
				break;
		} else {
			foundEventLess = true;
			if (foundWithEvent)
				break;
		}
		if (HAS_ATTR(transElem, "target")) {
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
		eventNames = getCommonEvents(transitionSet);
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

	// extract conditions
	std::list<std::string> conditions;
	for (int i = 0; i < transitionSet.size(); i++) {
		Arabica::DOM::Element<std::string> transElem = Arabica::DOM::Element<std::string>(transitionSet[i]);
		// gather conditions while we are iterating anyway
		if (HAS_ATTR(transElem, "cond")) {
			conditions.push_back(ATTR(transElem, "cond"));
		}
	}
	
	int index = 0;
	seperator = "";
	for (std::vector<Element<std::string> >::iterator transIter = interpreter->indexedTransitions.begin(); transIter != interpreter->indexedTransitions.end(); transIter++) {
		const Element<std::string>& refTrans = *transIter;
		if (InterpreterImpl::isMember(refTrans, transitionSet)) {
			members += seperator + toStr(index);
		} else {
			members += seperator;
			for (int i = 0; i < toStr(index).size(); i++) {
				members += " ";
			}
		}
		seperator = " ";
		index++;
	}
	
	//	if (members == "        4   6 7    ")
	//		std::cout << "asdfadf";

	if (conditions.size() > 1) {
		condition = dataModel.andExpressions(conditions);
		if (condition.size() == 0) {
			LOG(ERROR) << "Datamodel does not support to conjungate expressions!" << std::endl;
		}
	} else if (conditions.size() == 1) {
		condition = conditions.front();
	}
}

Arabica::XPath::NodeSet<std::string> GlobalState::getActiveStates() {
	return interpreter->refsToStates(activeStatesRefs);
}

Arabica::XPath::NodeSet<std::string> GlobalState::getAlreadyEnteredStates() {
	return interpreter->refsToStates(alreadyEnteredStatesRefs);
}

std::map<std::string, Arabica::XPath::NodeSet<std::string> > GlobalState::getHistoryStates() {
	std::map<std::string, Arabica::XPath::NodeSet<std::string> > historyValue;
	for (std::map<std::string, std::set<int> >::iterator histIter = historyStatesRefs.begin(); histIter != historyStatesRefs.end(); histIter++) {
		historyValue[histIter->first] = interpreter->refsToStates(histIter->second);
	}
	return historyValue;
}

	
Arabica::XPath::NodeSet<std::string> GlobalTransition::getTransitions() const {
	return interpreter->refsToTransitions(transitionRefs);
}

std::list<std::string> GlobalTransition::getCommonEvents(const NodeSet<std::string>& transitions) {
	std::list<std::string> prefixes;
	std::list<std::string> longestPrefixes;

	for (int i = 0; i < transitions.size(); i++) {
		// for every transition
		std::list<std::string> eventNames = InterpreterImpl::tokenizeIdRefs(ATTR_CAST(transitions[i], "event"));

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
				if (!InterpreterImpl::nameMatch(ATTR_CAST(transitions[j], "event"), eventName)) {
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
			if (!iequals(*outerEventNameIter, *innerEventNameIter) && InterpreterImpl::nameMatch(*outerEventNameIter, *innerEventNameIter)) {
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
