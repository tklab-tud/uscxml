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
#include "uscxml/debug/Complexity.h"

#include <DOM/SAX2DOM/SAX2DOM.hpp>
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

#define DUMP_STATS(nrTrans, disregardTime) \
uint64_t now = tthread::chrono::system_clock::now(); \
if (now - _lastTimeStamp > 1000 || disregardTime) { \
	std::cerr << "## Transition: " << _perfTransUsed << " / " << _perfTransTotal << " [" << _perfTransProcessed << "/sec]"; \
	if (nrTrans > 0) { \
		std::cerr << " - 2**" << nrTrans << " = " << pow(2.0, static_cast<double>(nrTrans)); \
	} \
	std::cerr << std::endl; \
	std::cerr << "## State     : " <<  _globalConf.size() << " found / " << _perfStackSize << " stacked / " << _perfStatesTotal << " seen [" << _perfStatesProcessed << "/sec]" << std::endl; \
	std::cerr << "## Microstep : " << _perfMicroStepTotal << " [" << _perfMicroStepProcessed << "/sec]" << std::endl; \
	std::cerr << "## Cached    : " << _perfStatesCachedTotal << " [" << _perfStatesCachedProcessed << "/sec]" << std::endl; \
	std::cerr << "## Skipped   : " << _perfStatesSkippedTotal << " [" << _perfStatesSkippedProcessed << "/sec]" << std::endl; \
	std::cerr << "## Queues    : " << (_maxEventRaisedChain == UNDECIDABLE ? "UNK" : toStr(_maxEventRaisedChain)) << " / " << (_maxEventSentChain == UNDECIDABLE ? "UNK" : toStr(_maxEventSentChain)) << std::endl; \
	std::cerr << "toFSM: "; \
	std::cerr << _perfTransUsed << ", " << _perfTransTotal << ", " << _perfTransProcessed << ", "; \
	std::cerr << _globalConf.size() << ", " << _perfStackSize << ", " << _perfStatesTotal << ", " << _perfStatesProcessed << ", "; \
	std::cerr << _perfMicroStepTotal << ", " << _perfMicroStepProcessed << ", "; \
	std::cerr << _perfStatesCachedTotal << ", " << _perfStatesCachedProcessed << ", " << _perfStatesSkippedTotal << ", " << _perfStatesSkippedProcessed << ", "; \
	std::cerr << (_maxEventRaisedChain == UNDECIDABLE ? "UNK" : toStr(_maxEventRaisedChain)) << ", " << (_maxEventSentChain == UNDECIDABLE ? "UNK" : toStr(_maxEventSentChain)) << std::endl; \
	std::cerr << std::endl; \
	_perfTransProcessed = 0; \
	_perfStatesProcessed = 0; \
	_perfStatesCachedProcessed = 0; \
	_perfStatesSkippedProcessed = 0; \
	_perfMicroStepProcessed = 0; \
	if (!disregardTime)\
		_lastTimeStamp = now; \
}

//std::cerr << "Q: " << (_maxEventRaisedChain == UNDECIDABLE ? "UNK" : toStr(_maxEventRaisedChain)) << " / " << (_maxEventSentChain == UNDECIDABLE ? "UNK" : toStr(_maxEventSentChain)) << std::endl;

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



ChartToFSM::ChartToFSM(const Interpreter& other) {

	cloneFrom(other.getImpl());

	_transitionsFromTree = true;
	_keepInvalidTransitions = false;
	_lastTimeStamp = tthread::chrono::system_clock::now();
	_perfTransProcessed = 0;
	_perfTransTotal = 0;
	_perfTransUsed = 0;
	_perfStatesTotal = 0;
	_perfStatesProcessed = 0;
	_perfStackSize = 0;
	_perfStatesSkippedProcessed = 0;
	_perfStatesSkippedTotal = 0;
	_perfStatesCachedProcessed = 0;
	_perfStatesCachedTotal = 0;
	_perfMicroStepProcessed = 0;
	_perfMicroStepTotal = 0;

	if (envVarIEquals("USCXML_TRANSFORM_TRANS_FROM", "powerset"))
		_transitionsFromTree = false;

	_start = NULL;
	_currGlobalTransition = NULL;
	_transTree = NULL;

	_lastStateIndex = 0;
	_lastActiveIndex = 0;
	_lastTransIndex = 0;

	_maxEventSentChain = 0;
	_maxEventRaisedChain = 0;
	_doneEventRaiseTolerance = 0;
	_skipEventChainCalculations = false;

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
	Arabica::XPath::NodeSet<std::string> allTransitions = DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "transition", _scxml, true);
	for (int i = 0; i < allTransitions.size(); i++) {
		_transParents.erase(allTransitions[i]);
	}
}

Document<std::string> ChartToFSM::getDocument() const {
	if (_flatDoc)
		return _flatDoc;
	return _document;
}

InterpreterState ChartToFSM::interpret() {

	init();
	setupIOProcessors();

	{
		std::list<std::set<Element<std::string> > > allConfig = Complexity::getAllConfigurations(_scxml);
		for (std::list<std::set<Element<std::string> > >::iterator confIter = allConfig.begin(); confIter != allConfig.end(); confIter++) {
			std::string seperator;
			NodeSet<std::string> configNodeSet;
			std::set<Element<std::string> > config = *confIter;
			for (std::set<Element<std::string> >::iterator elemIter = config.begin(); elemIter != config.end(); elemIter++) {
//				std::cerr << seperator << ATTR((*elemIter), "id");
				seperator = ",";
				configNodeSet.push_back(*elemIter);
			}
			assert(isLegalConfiguration(configNodeSet));
//			std::cerr << std::endl;
		}
	}
	std::map<size_t, size_t> histoGramm = Complexity::getTransitionHistogramm(_scxml);
//	abort();

	uint64_t complexity = Complexity::stateMachineComplexity(this) + 1;
	std::cerr << "Approximate Complexity: " << complexity << std::endl;
	std::cerr << "Approximate Active Complexity: " << Complexity::stateMachineComplexity(this, Complexity::IGNORE_HISTORY | Complexity::IGNORE_NESTED_DATA) + 1  << std::endl;

	if (complexity > 1000) {
		_skipEventChainCalculations = true;
		_maxEventRaisedChain = UNDECIDABLE;
		_maxEventSentChain = UNDECIDABLE;
	}
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
		Arabica::XPath::NodeSet<std::string> allTransitions = DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "transition", _scxml, true);
		indexedTransitions.reserve(allTransitions.size());
		for (int i = 0; i < allTransitions.size(); i++) {
			_transParents[allTransitions[i]] = InterpreterImpl::getParentState(allTransitions[i]);
		}
	}

	// identify all history elements
	NodeSet<std::string> histories = DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "history", _scxml, true);
	for (int i = 0; i < histories.size(); i++) {
		_historyTargets[ATTR_CAST(histories[i], "id")] = Element<std::string>(histories[i]);
	}

	_binding = (HAS_ATTR(_scxml, "binding") && iequals(ATTR(_scxml, "binding"), "late") ? LATE : EARLY);
	_alreadyFlat = (HAS_ATTR(_scxml, "flat") && stringIsTrue(ATTR(_scxml, "flat")));

	if (_alreadyFlat) {
		reassembleFromFlat();
		return _state;
	}

	// set invokeid for all invokers to parent state if none given
	NodeSet<std::string> invokers = DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "invoke", _scxml, true);
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

	if (!_skipEventChainCalculations)
		annotateRaiseAndSend(_scxml);

//	std::cout << _scxml << std::endl;

	indexTransitions();

	// add initial transitions as least prior
	for (int i = 0; i < initialTransitions.size() ; i++) {
		indexedTransitions.push_back(Element<std::string>(initialTransitions[i]));
	}

	// set index attribute for transitions
	for (int i = 0; i < indexedTransitions.size(); i++) {
//		std::cerr << toStr(i) << ":" << (HAS_ATTR(indexedTransitions[i], "line_start") ? ATTR(indexedTransitions[i], "line_start") : "");
//		std::cerr << "\t" << DOMUtils::xPathForNode(indexedTransitions[i]) << std::endl;
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

	// create a _flatDoc for the FSM
	DOMImplementation<std::string> domFactory = Arabica::SimpleDOM::DOMImplementation<std::string>::getDOMImplementation();
	_flatDoc = domFactory.createDocument(_document.getNamespaceURI(), "", 0);

	GlobalTransition* globalTransition = new GlobalTransition(initialTransitions, _dataModel, this);
	globalTransition->index = _lastTransIndex++;

	_start->sortedOutgoing.push_back(globalTransition);
	globalTransition->source = _start->stateId;
	_currGlobalTransition = globalTransition;

	enterStates(initialTransitions);
	globalTransition->destination = FlatStateIdentifier::toStateId(_configuration);
	globalTransition->activeDestination = globalTransition->destination;

	explode();

	DUMP_STATS(0, true);

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
	std::cerr << "Actual Active Complexity: " << _activeConf.size() << std::endl;
	std::cerr << "Internal Queue: " << _maxEventRaisedChain << std::endl;
	std::cerr << "External Queue: " << _maxEventSentChain << std::endl;

//	if (complexity < _globalConf.size())
//		throw std::runtime_error("Upper bound for states exceeded");

	return _state;
}

void ChartToFSM::executeContent(const Arabica::DOM::Element<std::string>& content, bool rethrow) {
//	std::cerr << content << std::endl;
//	std::cerr << TAGNAME(content) << std::endl;

	GlobalTransition::Action action;

	NodeList<std::string> childs = content.getChildNodes();
	for (unsigned int i = 0; i < childs.getLength(); i++) {
		Node_base::Type type = childs.item(i).getNodeType();
		if (type == Node_base::ELEMENT_NODE || type == Node_base::COMMENT_NODE || type == Node_base::TEXT_NODE) {
			goto HAS_VALID_CHILDREN;
		}
	}
	return;

HAS_VALID_CHILDREN:
	if (false) {
	} else if (TAGNAME(content) == "transition") {
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

	if (!_skipEventChainCalculations &&
	        (_maxEventRaisedChain != UNDECIDABLE || _maxEventSentChain != UNDECIDABLE)) {
		assert(content.hasAttribute("raise") && content.hasAttribute("send"));

		std::string raiseAttr = content.getAttribute("raise");
		std::string sendAttr = content.getAttribute("send");

		_currGlobalTransition->eventsRaised = (raiseAttr == "-1" ? UNDECIDABLE : _currGlobalTransition->eventsRaised + strTo<uint32_t>(raiseAttr));
		_currGlobalTransition->eventsSent = (sendAttr == "-1" ? UNDECIDABLE : _currGlobalTransition->eventsSent + strTo<uint32_t>(sendAttr));

		if (_currGlobalTransition->eventsRaised > _maxEventRaisedChain)
			_maxEventRaisedChain = _currGlobalTransition->eventsRaised;
		if (_currGlobalTransition->eventsSent > _maxEventSentChain)
			_maxEventSentChain = _currGlobalTransition->eventsSent;
	}

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

void ChartToFSM::internalDoneSend(const Arabica::DOM::Element<std::string>& state, const Arabica::DOM::Element<std::string>& doneData) {
	if (!isState(state))
		return;

//    if (LOCALNAME(state) == "scxml")
//        return;

//	if (parentIsScxmlState(state))
//		return;

//	return;
//	std::cerr << "internalDoneSend: " << state << std::endl;

	// create onentry with a raise element
	Element<std::string> onentry = _flatDoc.createElementNS(_nsInfo.nsURL, "onentry");
	_nsInfo.setPrefix(onentry);

	Element<std::string> raise = _flatDoc.createElementNS(_nsInfo.nsURL, "raise");
	_nsInfo.setPrefix(raise);

	onentry.appendChild(raise);

	if (doneData) {
		Arabica::XPath::NodeSet<std::string> contents = DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "content", doneData);
		if (contents.size() > 0) {
			Node<std::string> imported = _flatDoc.importNode(contents[0], true);
			raise.appendChild(imported);
		}
		Arabica::XPath::NodeSet<std::string> params = DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "param", doneData);
		if (params.size() > 0) {
			Node<std::string> imported = _flatDoc.importNode(params[0], true);
			raise.appendChild(imported);
		}
	}


	raise.setAttribute("event", "done.state." + ATTR_CAST(state, "id")); // parent?!

	GlobalTransition::Action action;
	action.raiseDone = onentry; // HERE!

	_currGlobalTransition->actions.push_back(action);
	if (!_skipEventChainCalculations &&
	        (_maxEventRaisedChain != UNDECIDABLE || _maxEventSentChain != UNDECIDABLE))
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

static bool filterSameHierarchy(const NodeSet<std::string>& transitions) {
	for (unsigned int i = 0; i < transitions.size(); i++) {
		Node<std::string> t1 = transitions[i];
		Node<std::string> p1 = InterpreterImpl::getParentState(t1);
		for (unsigned int j = i + 1; j < transitions.size(); j++) {
			Node<std::string> t2 = transitions[j];
			Node<std::string> p2 = InterpreterImpl::getParentState(t2);
			while(p2) {
				if (p1 == p2) {
					return false;
				}
				p2 = p2.getParentNode();
			}
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
					if (nameMatch(eventDesc1, eventDesc2)) {
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
	execContent.push_back(DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "transition", _scxml, true));
	execContent.push_back(DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "onentry", _scxml, true));
	execContent.push_back(DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "onexit", _scxml, true));
	for (int i = 0; i < execContent.size(); i++) {
		Element<std::string> execContentElem(execContent[i]);

		int nrRaise = 0;
		NodeSet<std::string> raise = DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "raise", execContent[i], true);
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
		NodeSet<std::string> sends = DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "send", execContent[i], true);
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

void ChartToFSM::annotateDomain() {
	Arabica::XPath::NodeSet<std::string> allTransitions = DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "transition", _scxml, true);
	for (int i = 0; i < allTransitions.size(); i++) {
		Element<std::string> transition(allTransitions[i]);
		Arabica::DOM::Node<std::string> domain = getTransitionDomain(transition);
		if (domain) {
			transition.setAttribute("domain", (HAS_ATTR_CAST(domain, "id") ? ATTR_CAST(domain, "id") : DOMUtils::xPathForNode(domain)));
		} else {
			transition.setAttribute("domain", "#UNDEF");
		}
	}
}

void ChartToFSM::annotateExitSet() {
	Arabica::XPath::NodeSet<std::string> allTransitions = DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "transition", _scxml, true);
	for (int i = 0; i < allTransitions.size(); i++) {
		Element<std::string> transition(allTransitions[i]);
		Arabica::DOM::Node<std::string> domain = getTransitionDomain(transition);

		Arabica::XPath::NodeSet<std::string> allStates = getAllStates();
		std::ostringstream exitSetStr;
		std::string seperator = "";
		for (int j = 0; j < allStates.size(); j++) {
			Element<std::string> state(allStates[j]);
			if (state.getParentNode() == domain) {
				exitSetStr << seperator << (HAS_ATTR(state, "id") ? ATTR(state, "id") : DOMUtils::xPathForNode(state));
				seperator = ", ";
			}
		}
		transition.setAttribute("exitset", exitSetStr.str());
	}
}

void ChartToFSM::annotateEntrySet() {
	Arabica::XPath::NodeSet<std::string> allTransitions = DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "transition", _scxml, true);
	for (int i = 0; i < allTransitions.size(); i++) {
		Element<std::string> transition(allTransitions[i]);

		NodeSet<std::string> tmpTransitions;
		NodeSet<std::string> tmpStatesToEnter;
		NodeSet<std::string> tmpStatesForDefaultEntry;
		std::map<std::string, Arabica::DOM::Node<std::string> > tmpDefaultHistoryContent;

		tmpTransitions.push_back(transition);
		computeEntrySet(tmpTransitions, tmpStatesToEnter, tmpStatesForDefaultEntry, tmpDefaultHistoryContent);

		std::ostringstream entrySetStr;
		std::string seperator = "";

		for (int j = 0; j < tmpStatesToEnter.size(); j++) {
			Element<std::string> state(tmpStatesToEnter[j]);
			entrySetStr << seperator << (HAS_ATTR(state, "id") ? ATTR(state, "id") : DOMUtils::xPathForNode(state));
			seperator = ", ";
		}
		for (int j = 0; j < tmpStatesForDefaultEntry.size(); j++) {
			Element<std::string> state(tmpStatesForDefaultEntry[j]);
			entrySetStr << seperator << (HAS_ATTR(state, "id") ? ATTR(state, "id") : DOMUtils::xPathForNode(state));
			seperator = ", ";
		}
		transition.setAttribute("entryset", entrySetStr.str());

	}
}

void ChartToFSM::annotateConflicts() {
	Arabica::XPath::NodeSet<std::string> allTransitions = DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "transition", _scxml, true);
	Arabica::XPath::NodeSet<std::string> allStates = getAllStates();

	for (int i = 0; i < allTransitions.size(); i++) {
		Element<std::string> t1(allTransitions[i]);
		if (!isState(Element<std::string>(t1.getParentNode())))
			continue;

		Arabica::DOM::Node<std::string> d1 = getTransitionDomain(t1);

		Arabica::XPath::NodeSet<std::string> exitSet1;
		for (int k = 0; k < allStates.size(); k++) {
			Element<std::string> state(allStates[k]);
			if (isDescendant(state, d1)) {
				exitSet1.push_back(state);
			}
		}

		std::ostringstream preemptionStr;
		std::string seperator = "";

		for (int j = 0; j < allTransitions.size(); j++) {
			if ( i == j)
				continue;

			Element<std::string> t2(allTransitions[j]);
			if (!isState(Element<std::string>(t2.getParentNode())))
				continue;

			Arabica::DOM::Node<std::string> d2 = getTransitionDomain(t2);

			Arabica::XPath::NodeSet<std::string> exitSet2;
			for (int k = 0; k < allStates.size(); k++) {
				Element<std::string> state(allStates[k]);
				if (isDescendant(state, d2)) {
					exitSet2.push_back(state);
				}
			}

			if (hasIntersection(exitSet1, exitSet2)) {
				preemptionStr << seperator << (HAS_ATTR(t2, "priority") ? ATTR(t2, "priority") : DOMUtils::xPathForNode(t2));
				seperator = ", ";
			}

//            if (isDescendant(d1, d2) || isDescendant(d2, d1) || d1 == d2) {
//                preemptionStr << seperator << ATTR(t2, "priority");
//                seperator = ", ";
//            }

		}
		if (preemptionStr.str().size() > 0)
			t1.setAttribute("conflicts", preemptionStr.str());

	}
}

void ChartToFSM::indexTransitions() {
	indexedTransitions.clear();
	indexTransitions(_scxml);

#if 1
	size_t index = indexedTransitions.size() - 1;
	for (std::vector<Arabica::DOM::Element<std::string> >::iterator transIter = indexedTransitions.begin(); transIter != indexedTransitions.end(); transIter++) {
		transIter->setAttribute("priority", toStr(index));
		index--;
	}
#else
	size_t index = 0;
	for (std::vector<Arabica::DOM::Element<std::string> >::iterator transIter = indexedTransitions.begin(); transIter != indexedTransitions.end(); transIter++) {
		transIter->setAttribute("priority", toStr(index));
		index++;
	}
#endif
	// reverse indices for most prior to be in front
	//std::reverse(indexedTransitions.begin(), indexedTransitions.end());
}

#if 0
void ChartToFSM::indexTransitions(const Arabica::DOM::Element<std::string>& root) {
	// breadth first traversal of transitions
	Arabica::XPath::NodeSet<std::string> levelTransitions = DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "transition", root);
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

#else

void ChartToFSM::indexTransitions(const Arabica::DOM::Element<std::string>& root) {
	// Post-order traversal of transitions
	Arabica::XPath::NodeSet<std::string> childStates = getChildStates(root);
	for (int i = 0; i < childStates.size(); i++) {
		Element<std::string> childElem(childStates[i]);
		indexTransitions(childElem);
	}

	Arabica::XPath::NodeSet<std::string> levelTransitions = DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "transition", root);
	for (int i = 0; i < levelTransitions.size(); i++) {
		// push into index starting with least prior
		indexedTransitions.push_back(Element<std::string>(levelTransitions[i]));
	}

}

#endif
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
bool hasUnconditionalSuperset(GlobalTransition* first, GlobalTransition* second) {

	NodeSet<std::string> firstTransitions = first->getTransitions();
	NodeSet<std::string> secondTransitions = second->getTransitions();

//    if (first->condition.size() > 0)
//        return false;

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

/**
 * earlier transition is conditionless for same event
 */
bool hasEarlierUnconditionalMatch(GlobalTransition* first, GlobalTransition* second) {
	if (first->eventDesc == second->eventDesc) {
		if (first->condition.size() == 0)
			return true;
	}
	return false;
}

std::list<GlobalTransition*> redundantRemove(std::list<GlobalTransition*> list) {
#if 1
	std::list<GlobalTransition*>::iterator outerIter;
	std::list<GlobalTransition*>::iterator innerIter;

	outerIter = list.begin();
	while(outerIter != list.end()) {
		innerIter = outerIter;

		while(innerIter != list.end()) {
			if (innerIter == outerIter) {
				innerIter++;
				continue;
			}

			GlobalTransition* t1 = *outerIter;
			GlobalTransition* t2 = *innerIter;

			if (hasUnconditionalSuperset(t1, t2)) {
				list.erase(innerIter++);
				continue;
			} else if (hasUnconditionalSuperset(t2, t1)) {
				list.erase(outerIter++);
				break;
			}
			if (hasEarlierUnconditionalMatch(t1, t2)) {
				list.erase(innerIter++);
				continue;
			}
			innerIter++;
		}

		outerIter++;
	}

#else

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
				innerIter = list.erase(innerIter);
				continue;
			} else if (hasUnconditionalSuperset(t2, t1)) {
				outerIter = list.erase(outerIter);
				continue;
			}
			if (hasEarlierUnconditionalMatch(t1, t2)) {
				innerIter = list.erase(innerIter);
				continue;
			}
		}
	}
#endif
	return list;
}

std::list<GlobalTransition*> redundantMark(std::list<GlobalTransition*> list) {
#if 1
	std::list<GlobalTransition*>::iterator outerIter;
	std::list<GlobalTransition*>::iterator innerIter;

	outerIter = list.begin();
	while(outerIter != list.end()) {
		innerIter = outerIter;

		while(innerIter != list.end()) {
			if (innerIter == outerIter) {
				innerIter++;
				continue;
			}

			GlobalTransition* t1 = *outerIter;
			GlobalTransition* t2 = *innerIter;

			if (!t1->isValid || !t2->isValid) {
				innerIter++;
				continue;
			}

			if (hasUnconditionalSuperset(t1, t2)) {
				t2->isValid = false;
				t2->invalidMsg = "Unconditional superset";
				t2->invalidReason = GlobalTransition::UNCONDITIONAL_SUPERSET;
				innerIter++;
				continue;
			} else if (hasUnconditionalSuperset(t2, t1)) {
				t1->isValid = false;
				t1->invalidMsg = "Unconditional superset";
				t1->invalidReason = GlobalTransition::UNCONDITIONAL_SUPERSET;
				outerIter++;
				break;
			}
			if (hasEarlierUnconditionalMatch(t1, t2)) {
				t2->isValid = false;
				t2->invalidMsg = "Earlier unconditional match";
				t2->invalidReason = GlobalTransition::UNCONDITIONAL_MATCH;
				innerIter++;
				continue;
			}
			innerIter++;
		}

		outerIter++;
	}

#else

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

			if (!t1->isValid || !t2->isValid)
				continue;

			if (hasUnconditionalSuperset(t1, t2)) {
				t2->isValid = false;
				t2->invalidMsg = "Unconditional superset";
				t2->invalidReason = GlobalTransition::UNCONDITIONAL_SUPERSET;
				continue;
			} else if (hasUnconditionalSuperset(t2, t1)) {
				t1->isValid = false;
				t1->invalidMsg = "Unconditional superset";
				t1->invalidReason = GlobalTransition::UNCONDITIONAL_SUPERSET;
				continue;
			}
			if (hasEarlierUnconditionalMatch(t1, t2)) {
				t2->isValid = false;
				t2->invalidMsg = "Earlier unconditional match";
				t2->invalidReason = GlobalTransition::UNCONDITIONAL_MATCH;
				continue;
			}
		}
	}
#endif
	return list;
}


void TransitionTreeNode::dump(int indent) {
	std::string padding;
	for (int i = 0; i + 1 < indent; i++) {
		padding += "| ";
	}
	if (indent > 0)
		padding += "|-";

	std::string typeString;
	switch (type) {
	case TYPE_NESTED:
		typeString = "NESTED";
		break;
	case TYPE_PARALLEL:
		typeString = "PARALLEL";
		break;
	case TYPE_TRANSITION:
		typeString = "TRANSITION";
		break;
	case TYPE_UNDEFINED:
		typeString = "UNDEFINED";
		break;
		break;
	default:
		break;
	}


	if (transition) {
		std::cerr << padding << "t" << ATTR(transition, "index") << " " << typeString << ": ";
//		std::cerr << (prevTransition != NULL ? " (" + prevTransition->nodeId + ") <-" : "");
		std::cerr << "[" << nodeId << "]";
//		std::cerr << (nextTransition != NULL ? " -> (" + nextTransition->nodeId + ")" : "");
		std::cerr << std::endl;
	} else {
		std::cerr << padding << ATTR(state, "id") << " " << typeString << ": " << "[" << nodeId << "]";
//		std::cerr << (firstTransition != NULL ? " -> " + firstTransition->nodeId : "");
		std::cerr << std::endl;
	}

	for (std::list<TransitionTreeNode*>::iterator childIter = children.begin(); childIter != children.end(); childIter++) {
		(*childIter)->dump(indent + 1);
	}
}

void ChartToFSM::getPotentialTransitionsForConfFromTree(const Arabica::XPath::NodeSet<std::string>& conf, std::map<std::string, GlobalTransition*>& outMap) {
	if (_transTree == NULL) {
		_transTree = buildTransTree(_scxml, "0");
//		_transTree->dump();
	}
	std::string seperator;


//	std::cerr << "--- ";

	// recursion start
	std::set<TransitionTreeNode*> transLeafs;

	for (int i = 0; i < conf.size(); i++) {
		DUMP_STATS(conf.size(), false);

		Element<std::string> confElem(conf[i]);
		assert(_stateToTransTreeNode.find(confElem) != _stateToTransTreeNode.end());
		TransitionTreeNode* node = _stateToTransTreeNode[confElem];
		if (node->firstState == NULL) { // a leaf - ignore intermediates
			// ascend to the first parent with transitions but stop at parallel nodes
			while(node != NULL && node->firstTransition == NULL) {
				if (node->parent && node->parent->type == TransitionTreeNode::TYPE_PARALLEL)
					break;
				node = node->parent;
			}
			if (node != NULL) {
				transLeafs.insert(node);
			} else {
				//std::cerr << ATTR(confElem, "id") << " does not cause transitions" << std::endl;
			}
		}
	}

	std::list<std::set<TransitionTreeNode*> > stack;
	stack.push_back(transLeafs); // push follow-up configurations onto stack

	while (stack.size() > 0) {
		// pop from front of stack
		std::set<TransitionTreeNode*> stateList = stack.front();
		stack.pop_front();

		DUMP_STATS(conf.size(), false);

#if 0
		seperator = "";
		std::cerr << "Current set: ";
		for (std::set<TransitionTreeNode*>::iterator transIter = stateList.begin(); transIter != stateList.end(); transIter++) {
			std::cerr << seperator << (*transIter)->nodeId;
			seperator = ", ";
		}
		std::cerr << std::endl;
#endif

		/*
		 * TransNodes contains a set of lists of transitions.
		 * In the inner stack we build every possible combination
		 * of picking at-most one from each list.
		 */

		/* create global transitions for every n-tuple in current set of lists */
		std::list<std::pair<std::set<TransitionTreeNode*>, std::set<TransitionTreeNode*> > > innerStack;
		innerStack.push_back(std::make_pair(std::set<TransitionTreeNode*>(), stateList));

		while(innerStack.size() > 0) {

			// picking at-most one from each list
			std::set<TransitionTreeNode*> remainingStates = innerStack.front().second;
			std::set<TransitionTreeNode*> fixedTransitions = innerStack.front().first;
			innerStack.pop_front();

			if (remainingStates.size() > 0) {
				// iterate for each first element fixed
				TransitionTreeNode* firstRemainingState = *remainingStates.begin();
				remainingStates.erase(remainingStates.begin());

				if (firstRemainingState->firstTransition == NULL) {
					// no transitions at this state - reenqueue with NULL selection from this
					innerStack.push_back(std::make_pair(fixedTransitions, remainingStates));
					continue;
				}

				TransitionTreeNode* currTrans = firstRemainingState->firstTransition;

				// choose none from firstList
				innerStack.push_back(std::make_pair(fixedTransitions, remainingStates));

				while(currTrans != NULL) {
					std::set<TransitionTreeNode*> fixedAndThis(fixedTransitions);
					fixedAndThis.insert(currTrans);
					innerStack.push_back(std::make_pair(fixedAndThis, remainingStates));
					currTrans = currTrans->nextTransition;
				}
			} else {
				DUMP_STATS(conf.size(), false);

				if (fixedTransitions.size() > 0) {

					_perfTransTotal++;
					_perfTransProcessed++;

					NodeSet<std::string> fixed;

#if 0
					seperator = "";
					for (std::set<TransitionTreeNode*>::iterator itemIter = fixedTransitions.begin(); itemIter != fixedTransitions.end(); itemIter++) {
						TransitionTreeNode* currItem = *itemIter;
						std::cerr << seperator << currItem->nodeId;
						seperator = ", ";
					}
					std::cerr << " ## ";
#endif

					seperator = "";
					for (std::set<TransitionTreeNode*>::iterator itemIter = fixedTransitions.begin(); itemIter != fixedTransitions.end(); itemIter++) {
						TransitionTreeNode* currItem = *itemIter;
						fixed.push_back(currItem->transition);
//						std::cerr << seperator << ATTR(currItem->transition, "index");
						seperator = ", ";
					}
//					std::cerr << std::endl;

					// fixed contains a transiton set!
					assert(filterSameState(fixed));
//					assert(filterChildEnabled(fixed));
					assert(filterSameHierarchy(fixed));
					// do not add if they preempt
					if (fixed.size() != removeConflictingTransitions(fixed).size()) {
//						std::cerr << " - PREEMPTS" << std::endl;
						continue;
					}

					GlobalTransition* transition = new GlobalTransition(fixed, _dataModel, this);
					transition->index = _lastTransIndex++;

//					assert(outMap.find(transition->transitionId) == outMap.end());

					if (!transition->isValid && !_keepInvalidTransitions) {
						delete(transition);
//						std::cerr << " - INVALID" << std::endl;
						continue;
					}

					_perfTransUsed++;

					outMap[transition->transitionId] = transition;
//					std::cerr << " - GOOD" << std::endl;
				}
			}
		}

		// create new set of transition lists by moving to parent states
		for (std::set<TransitionTreeNode*>::iterator stateIter = stateList.begin(); stateIter != stateList.end(); stateIter++) {
			TransitionTreeNode* origState = *stateIter;
			TransitionTreeNode* currState = origState;
			TransitionTreeNode* parentState = currState->parent;

			/**
			 * We ascend the current state via its parent and add the parent with transitions.
			 * However, we break if we reached the top or if we passed a parallel state for
			 * wich we are not the first child
			 */

			while(parentState != NULL) {
				if (parentState->type == TransitionTreeNode::TYPE_PARALLEL && parentState->firstState != currState) {
					// the first child of the parallel state will continue this transition - we made sure to keep them
					break;
				}

				if (parentState->firstTransition != NULL) {
//					std::cerr << "#### Adding new parent lists for " << origState->nodeId << std::endl;

					std::set<TransitionTreeNode*> newStateList;
					newStateList.insert(parentState);

					// add all other states that are not a child of the parent state
					for (std::set<TransitionTreeNode*>::iterator newlistIter = stateList.begin(); newlistIter != stateList.end(); newlistIter++) {
						TransitionTreeNode* otherState = *newlistIter;
						while(otherState != NULL && otherState != parentState) {
							otherState = otherState->parent;
						}
						if (otherState == NULL)
							newStateList.insert(*newlistIter);
					}
					if (newStateList.size() > 0)
						stack.push_back(newStateList);
					break;
				}

				currState = currState->parent;
				parentState = currState->parent;
			}
		}
	}
}

TransitionTreeNode* ChartToFSM::buildTransTree(const Arabica::DOM::Element<std::string>& root, const std::string& nodeId) {
	TransitionTreeNode* stateNode = new TransitionTreeNode();
	stateNode->nodeId = nodeId;
	stateNode->state = root;

	if (TAGNAME(root) == _nsInfo.xmlNSPrefix + "parallel") {
		stateNode->type = TransitionTreeNode::TYPE_PARALLEL;
	} else {
		stateNode->type = TransitionTreeNode::TYPE_NESTED;
	}

	// get all transitions and states from root without recursing
	NodeSet<std::string> nested;
	nested.push_back(DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "transition", root));
	nested.push_back(DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "state", root));
	nested.push_back(DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "final", root));
	nested.push_back(DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "parallel", root));
	nested.to_document_order();

	TransitionTreeNode* lastNode = NULL;

	for (int i = 0; i < nested.size(); i++) {
		Element<std::string> nestedElem(nested[i]);
		if (TAGNAME(nestedElem) == _nsInfo.xmlNSPrefix + "transition") {
			TransitionTreeNode* transNode = new TransitionTreeNode();
			transNode->transition = nestedElem;
			transNode->parent = stateNode;
			transNode->nodeId = nodeId + "-" + toStr(i);
			transNode->type = TransitionTreeNode::TYPE_TRANSITION;

			if (stateNode->firstTransition == NULL) {
				stateNode->firstTransition = transNode;
			}
			stateNode->children.push_back(transNode);
			stateNode->lastTransition = transNode;

			if (lastNode != NULL) {
				lastNode->nextTransition = transNode;
				transNode->prevTransition = lastNode;
			}
			lastNode = transNode;


		} else  {
			TransitionTreeNode* deeperNode = buildTransTree(nestedElem, nodeId + "-" + toStr(i));
			if (stateNode->firstState == NULL) {
				stateNode->firstState = deeperNode;
			}

			deeperNode->parent = stateNode;
			stateNode->children.push_back(deeperNode);
		}
	}

	_stateToTransTreeNode[root] = stateNode;

	return stateNode;
}

void ChartToFSM::getPotentialTransitionsForConfFromPowerSet(const Arabica::XPath::NodeSet<std::string>& conf, std::map<std::string, GlobalTransition*>& outMap) {
	// get all transition elements from states in the current configuration
	NodeSet<std::string> allTransitions = DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "transition", conf);

	{
		std::string seperator = "";
		for (int i = 0; i < allTransitions.size(); i++) {
			std::cerr << seperator << ATTR_CAST(allTransitions[i], "index");
			seperator=", ";
		}
		std::cerr << std::endl;
	}

//	if (true) {
//		outMap = _confToTransitions[""];
//	}

	if (allTransitions.size() == 0)
		return; // no transitions

	int nrElements = allTransitions.size();
	int k = 0;
	int* stack = (int*)malloc((nrElements + 1) * sizeof(int));
	memset(stack, 0, (nrElements + 1) * sizeof(int));

	/**
	 * Powerset is too naive and takes too long!
	 * We have it up to 500k checks/sec and still 2**30 is
	 * 1G+ for 30minutes in a single state out of 50k+!
	 */

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

		DUMP_STATS(nrElements, false);

		GlobalTransition* transition = NULL;

		// reduce to conflict-free subset
		// transitions.to_document_order();
		if (!_keepInvalidTransitions) {
			// remove transitions in the same state
			if(!filterSameState(transitions))
				continue;
			if (dump) DUMP_TRANSSET("after same state filtered");

			// remove those transitions with a child transition
//			if(!filterChildEnabled(transitions))
			if(!filterSameHierarchy(transitions))
				continue;
			if (dump) DUMP_TRANSSET("after child enabled filtered");

			transitions = removeConflictingTransitions(transitions);
			if (dump) DUMP_TRANSSET("after conflicting filtered");
			// algorithm can never reduce to empty set
			assert(transitions.size() > 0);

			// create a GlobalTransition object from the set
			transition = new GlobalTransition(transitions, _dataModel, this);
			if (!transition->isValid) {
				// this set of transitions can not be enabled together
				delete transition;
				continue;
			}
		} else {
			transition = new GlobalTransition(transitions, _dataModel, this);

			// remove transitions in the same state
			if(!filterSameState(transitions)) {
				transition->isValid = false;
				transition->invalidReason = GlobalTransition::SAME_SOURCE_STATE;
				transition->invalidMsg = "Same source state";

//			} else if(!filterChildEnabled(transitions)) {
			} else if(!filterSameHierarchy(transitions)) {
				transition->isValid = false;
				transition->invalidReason = GlobalTransition::CHILD_ENABLED;
				transition->invalidMsg = "Nested transitions";
			} else {
				NodeSet<std::string> nonPreemptingTransitions = removeConflictingTransitions(transitions);
				if (nonPreemptingTransitions.size() != transitions.size()) {
					transition->isValid = false;
					transition->invalidReason = GlobalTransition::PREEMPTING_MEMBERS;
					transition->invalidMsg = "Preempting members";
				}
			}

		}

		// two combinations might have projected onto the same conflict-free set
		if (outMap.find(transition->transitionId) != outMap.end()) {
			//			std::cerr << "skipping as projected onto existing conflict-free subset" << std::endl;
			delete transition;
			continue;
		}

		transition->index = _lastTransIndex++;
		_perfTransUsed++;

		// remember this conflict-free set
		//		std::cerr << "New conflict-free subset: " << transition->transitionId << ":" << transition->eventDesc << std::endl;
		outMap[transition->transitionId] = transition;
	}
//	_confToTransitions[""] = outMap;
	return;
}

void ChartToFSM::explode() {

	std::list<std::pair<GlobalTransition*, GlobalState*> > statesRemaining;
	statesRemaining.push_back(std::make_pair(_currGlobalTransition, new GlobalState(_configuration, _alreadyEntered, _historyValue, _nsInfo.xmlNSPrefix, this)));

	// add all invokers for initial transition
	for (unsigned int i = 0; i < _statesToInvoke.size(); i++) {
		NodeSet<std::string> invokes = DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "invoke", _statesToInvoke[i]);
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
		_perfStackSize = statesRemaining.size();
		_perfStatesTotal++;
		_perfStatesProcessed++;

		DUMP_STATS(0, false);

		GlobalState* globalState = statesRemaining.front().second;
		_currGlobalTransition = statesRemaining.front().first;
		statesRemaining.pop_front();

		// used to be conditionalized, we will just assume
		assert(_currGlobalTransition);

		if (_globalConf.find(globalState->stateId) != _globalConf.end()) {
			if (_currGlobalTransition->isEventless &&
			        !_skipEventChainCalculations &&
			        (_maxEventRaisedChain != UNDECIDABLE || _maxEventSentChain != UNDECIDABLE)) {
				// we arrived via a spontaneaous transition, do we need to update?
				updateRaisedAndSendChains(_globalConf[globalState->stateId], _currGlobalTransition, std::set<GlobalTransition*>());
			}
			delete globalState;
			_perfStatesSkippedTotal++;
			_perfStatesSkippedProcessed++;
			continue; // we have already been here
		}

		_configuration = globalState->getActiveStates();
		_alreadyEntered = globalState->getAlreadyEnteredStates();
		_historyValue = globalState->getHistoryStates();

		// remember as global configuration
		_globalConf[globalState->stateId] = globalState;
		_globalConf[globalState->stateId]->index = _lastStateIndex++;

		if(_globalConf[globalState->stateId]->isFinal) {
			if (_activeConf.find(globalState->activeId) == _activeConf.end()) {
				assert(globalState->activeIndex == -1);
				globalState->activeIndex = _lastActiveIndex++;
				_activeConf[globalState->activeId] = globalState; // remember as active configuration
				exitInterpreter();
			}
			continue; // done in this branch
		}

		if (_activeConf.find(globalState->activeId) != _activeConf.end()) {
			// we already know these transition sets, just copy over
			std::list<GlobalTransition*>::iterator sortTransIter = _activeConf[globalState->activeId]->sortedOutgoing.begin();
			while(sortTransIter != _activeConf[globalState->activeId]->sortedOutgoing.end()) {
				globalState->sortedOutgoing.push_back(GlobalTransition::copyWithoutExecContent(*sortTransIter));
				globalState->sortedOutgoing.back()->index = _lastTransIndex++;
				_perfTransUsed++;
				sortTransIter++;
			}
			_perfStatesCachedTotal++;
			_perfStatesCachedProcessed++;

		} else {
			// we need to calculate the potential optimal transition sets
			std::map<std::string, GlobalTransition*> transitionSets;
			//			std::cerr << globalState->stateId << std::endl;
			if (_transitionsFromTree) {
				getPotentialTransitionsForConfFromTree(refsToStates(globalState->activeStatesRefs), transitionSets);
			} else {
				getPotentialTransitionsForConfFromPowerSet(refsToStates(globalState->activeStatesRefs), transitionSets);
			}

			// reduce and sort transition sets
			for(std::map<std::string, GlobalTransition*>::iterator transSetIter = transitionSets.begin();
			        transSetIter != transitionSets.end();
			        transSetIter++) {
				globalState->sortedOutgoing.push_back(transSetIter->second);
			}

			globalState->sortedOutgoing.sort(PtrComp<GlobalTransition>);
//			globalState->sortedOutgoing.unique(hasUnconditionalSuperset);
//			globalState->sortedOutgoing.unique(hasEarlierUnconditionalMatch);
			// unique is not quite like what we need, but it was a start
			if (_keepInvalidTransitions) {
				globalState->sortedOutgoing = redundantMark(globalState->sortedOutgoing);
			} else {
//				globalState->sortedOutgoing.unique(hasUnconditionalSuperset);
//				globalState->sortedOutgoing.unique(hasEarlierUnconditionalMatch);
				globalState->sortedOutgoing = redundantRemove(globalState->sortedOutgoing);
			}
//			globalState->sortedOutgoing = redundantRemove(globalState->sortedOutgoing);
//			globalState->sortedOutgoing = redundantRemove(globalState->sortedOutgoing);
//
//			std::cout << globalState->sortedOutgoing.size() << std::endl;

			assert(_activeConf.find(globalState->activeId) == _activeConf.end());
			assert(globalState->activeIndex == -1);
			globalState->activeIndex = _lastActiveIndex++;
			_activeConf[globalState->activeId] = globalState;
		}

		// take every transition set and append resulting new state
		for(std::list<GlobalTransition*>::iterator transIter = globalState->sortedOutgoing.begin();
		        transIter != globalState->sortedOutgoing.end();
		        transIter++) {

			GlobalTransition* incomingTrans = _currGlobalTransition;
			GlobalTransition* outgoingTrans = *transIter;

			outgoingTrans->source = globalState->stateId;

			if (_keepInvalidTransitions && !outgoingTrans->isValid)
				continue;

			_currGlobalTransition = outgoingTrans;

			microstep(refsToTransitions(outgoingTrans->transitionRefs));
//			assert(isLegalConfiguration(_configuration));

			_perfMicroStepProcessed++;
			_perfMicroStepTotal++;

			// if outgoing transition is spontaneous, add number of events to chain
			if (outgoingTrans->isEventless &&
			        !_skipEventChainCalculations &&
			        (_maxEventRaisedChain != UNDECIDABLE || _maxEventSentChain != UNDECIDABLE)) {
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
				NodeSet<std::string> invokes = DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "invoke", _statesToInvoke[i]);
				for (unsigned int j = 0; j < invokes.size(); j++) {
					invoke(Element<std::string>(invokes[j]));
				}
			}
			_statesToInvoke = NodeSet<std::string>();

			// remember that the last transition lead here
			outgoingTrans->destination = statesRemaining.back().second->stateId;
			outgoingTrans->activeDestination = statesRemaining.back().second->activeId;
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

void ChartToFSM::reassembleFromFlat() {
	LOG(ERROR) << "Cannot flatten flat SCXML document";
	abort();
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

std::ostream& operator<< (std::ostream& os, const GlobalTransition::Action& action) {
	if (action.onEntry)
		os << "onEntry: " << action.onEntry;
	if (action.onExit)
		os << "onExit: " << action.onExit;
	if (action.transition)
		os << "transition: " << action.transition;
	if (action.entered)
		os << "entered: " << action.entered;
	if (action.exited)
		os << "exited: " << action.exited;
	if (action.invoke)
		os << "invoke: " << action.invoke;
	if (action.uninvoke)
		os << "uninvoke: " << action.uninvoke;
	if (action.raiseDone)
		os << "raiseDone: " << action.raiseDone;
	return os;
}

GlobalState::GlobalState(const Arabica::XPath::NodeSet<std::string>& activeStates_,
                         const Arabica::XPath::NodeSet<std::string>& alreadyEnteredStates_, // we need to remember for binding=late
                         const std::map<std::string, Arabica::XPath::NodeSet<std::string> >& historyStates_,
                         const std::string& xmlNSPrefix,
                         ChartToFSM* flattener) {
	interpreter = flattener;
	activeIndex = -1;

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

GlobalTransition* GlobalTransition::copyWithoutExecContent(GlobalTransition* other) {
	GlobalTransition* newTrans = new GlobalTransition(*other);
	newTrans->actions.clear();
	newTrans->historyBase = other;
	other->historyTrans.push_back(newTrans);
	return newTrans;
}

GlobalTransition::GlobalTransition(const Arabica::XPath::NodeSet<std::string>& transitionSet, DataModel dataModel, ChartToFSM* flattener) {
	interpreter = flattener;

	eventsRaised = 0;
	eventsSent = 0;
	eventsChainRaised = 0;
	eventsChainSent = 0;
	historyBase = NULL;

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

	Arabica::DOM::Element<std::string> withEvent;
	Arabica::DOM::Element<std::string> noneEvent;
	Arabica::DOM::Element<std::string> withTarget;
	Arabica::DOM::Element<std::string> noneTarget;

	for (int i = 0; i < transitionSet.size(); i++) {
		Arabica::DOM::Element<std::string> transElem = Arabica::DOM::Element<std::string>(transitionSet[i]);
		if (HAS_ATTR(transElem, "eventexpr")) {
			ERROR_EXECUTION_THROW("Cannot flatten document with eventexpr attributes");
		}
		if (HAS_ATTR(transElem, "event")) {
			foundWithEvent = true;
			withEvent = transElem;
			if (foundEventLess)
				break;
		} else {
			foundEventLess = true;
			noneEvent = transElem;
			if (foundWithEvent)
				break;
		}
		if (HAS_ATTR(transElem, "target")) {
			foundWithTarget = true;
			withTarget = transElem;
			if (foundTargetLess)
				break;
		} else {
			foundTargetLess = true;
			noneTarget = transElem;
			if (foundWithTarget)
				break;
		}

	}

	// do not mix eventless and event transitions
	if (foundEventLess && foundWithEvent) {
		if (flattener->_keepInvalidTransitions) {
			invalidReason = MIXES_EVENT_SPONTANEOUS;
			invalidMsg = "Mixes (non-)spontaneous";
		}
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
			if (flattener->_keepInvalidTransitions) {
				invalidReason = NO_COMMON_EVENT;
				invalidMsg = "No common event";
			}
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

	// extract conditions and history targets
	std::list<std::string> conditions;
	for (int i = 0; i < transitionSet.size(); i++) {
		Arabica::DOM::Element<std::string> transElem = Arabica::DOM::Element<std::string>(transitionSet[i]);
		// gather conditions while we are iterating anyway
		if (HAS_ATTR(transElem, "cond")) {
			conditions.push_back(boost::trim_copy(ATTR(transElem, "cond")));
		}

		std::list<std::string> targets = tokenize(ATTR(transElem, "target"));
		std::list<std::string>::iterator targetIter = targets.begin();
		while(targetIter != targets.end()) {
//			std::cout << "// " << *targetIter << std::endl;
			if (flattener->_historyTargets.find(*targetIter) != flattener->_historyTargets.end()) {
				histTargets.insert(*targetIter);
			}
			targetIter++;
		}
//		std::cout << std::endl << std::endl;
	}

	seperator = "";
	for (std::vector<Element<std::string> >::iterator transIter = interpreter->indexedTransitions.begin(); transIter != interpreter->indexedTransitions.end(); transIter++) {
		const Element<std::string>& refTrans = *transIter;
		if (!HAS_ATTR(refTrans, "priority"))
			continue;
		if (InterpreterImpl::isMember(refTrans, transitionSet)) {
			members += seperator + ATTR(refTrans, "priority");
		} else {
			members += seperator;
			for (int i = 0; i < ATTR(refTrans, "priority").size(); i++) {
				members += " ";
			}
		}
		seperator = " ";
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
		std::list<std::string> eventNames = tokenize(ATTR_CAST(transitions[i], "event"));

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
				if (!nameMatch(ATTR_CAST(transitions[j], "event"), eventName)) {
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
			if (!iequals(*outerEventNameIter, *innerEventNameIter) && nameMatch(*outerEventNameIter, *innerEventNameIter)) {
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
