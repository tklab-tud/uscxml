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
#include "uscxml/concurrency/DelayedEventQueue.h"

#include <glog/logging.h>
#include "uscxml/UUID.h"
#include "uscxml/DOMUtils.h"

#define VERBOSE 0

namespace uscxml {

using namespace Arabica::XPath;
using namespace Arabica::DOM;

size_t padding = 0;

std::string getPadding() {
	std::string pad = "";
	for (int i = 0; i < padding; i++) {
		pad += "  ";
	}
	return pad;
}

Arabica::XPath::NodeSet<std::string> InterpreterRC::removeConflictingTransitions(const Arabica::XPath::NodeSet<std::string>& enabledTransitions) {
	Arabica::XPath::NodeSet<std::string> filteredTransitions;

	for (unsigned int i = 0; i < enabledTransitions.size(); i++) {
		Element<std::string> t1(enabledTransitions[i]);
		bool t1Preempted = false;
		Arabica::XPath::NodeSet<std::string> transitionsToRemove;

		for (unsigned int j = 0; j < filteredTransitions.size(); j++) {
			Element<std::string> t2(enabledTransitions[j]);
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
			filteredTransitions.insert(filteredTransitions.end(), tmp.begin(), tmp.end());

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
					if (isAtomic(Element<std::string>(_configuration[k])) && isDescendant(_configuration[k], statesToExit[i]))
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


Arabica::XPath::NodeSet<std::string> InterpreterRC::computeExitSet(const Arabica::XPath::NodeSet<std::string>& transitions) {
	NodeSet<std::string> statesToExit;
	for (unsigned int i = 0; i < transitions.size(); i++) {
		Element<std::string> t(transitions[i]);
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
#if VERBOSE
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
			executeContent(transitions);
		}
		if (defaultHistoryContent.find(ATTR(s, "id")) != defaultHistoryContent.end()) {
			executeContent(Element<std::string>(defaultHistoryContent[ATTR(s, "id")]));
		}

		if (isFinal(s)) {
			internalDoneSend(s);
			if (parentIsScxmlState(s)) {
				_topLevelFinalReached = true;
			} else {
				Element<std::string> parent = (Element<std::string>)s.getParentNode();
				Element<std::string> grandParent = (Element<std::string>)parent.getParentNode();

				internalDoneSend(parent);

				if (isParallel(grandParent)) {
					Arabica::XPath::NodeSet<std::string> childs = getChildStates(grandParent);
					bool inFinalState = true;
					for (int j = 0; j < childs.size(); j++) {
						if (!isInFinalState(Element<std::string>(childs[j]))) {
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


void InterpreterRC::computeEntrySet(const Arabica::XPath::NodeSet<std::string>& transitions,
                                    NodeSet<std::string>& statesToEnter,
                                    NodeSet<std::string>& statesForDefaultEntry,
                                    std::map<std::string, Arabica::DOM::Node<std::string> > defaultHistoryContent) {

#if 1
	for (int i = 0; i < transitions.size(); i++) {
		Element<std::string> t(transitions[i]);
		
		NodeSet<std::string> targets = getTargetStates(t);
		
#if VERBOSE
		std::cout << "computeEntrySet: ";
		for (int i = 0; i < targets.size(); i++) {
			std::cout << ATTR_CAST(targets[i], "id") << " ";
		}
		std::cout << std::endl;
#endif


		for (int j = 0; j < targets.size(); j++) {
			Element<std::string> s = Element<std::string>(targets[j]);
			addDescendantStatesToEnter(s,statesToEnter,statesForDefaultEntry, defaultHistoryContent);
		}

		for (int j = 0; j < targets.size(); j++) {
			Element<std::string> s = Element<std::string>(targets[j]);
			addDescendantStatesToEnter(s,statesToEnter,statesForDefaultEntry, defaultHistoryContent);
		}
		
#if VERBOSE
		std::cout << "after addDescendantStatesToEnter: ";
		for (int i = 0; i < statesToEnter.size(); i++) {
			std::cout << ATTR_CAST(statesToEnter[i], "id") << " ";
		}
		std::cout << std::endl;
#endif

		Element<std::string> ancestor = Element<std::string>(getTransitionDomain(t));
		NodeSet<std::string> effectiveTargetStates = getEffectiveTargetStates(t);

		for (int j = 0; j < effectiveTargetStates.size(); j++) {
			Element<std::string> s = Element<std::string>(effectiveTargetStates[j]);
			addAncestorStatesToEnter(s, ancestor, statesToEnter, statesForDefaultEntry, defaultHistoryContent);
		}

#if VERBOSE
		std::cout << "after addAncestorStatesToEnter: ";
		for (int i = 0; i < statesToEnter.size(); i++) {
			std::cout << ATTR_CAST(statesToEnter[i], "id") << " ";
		}
		std::cout << std::endl;
#endif

	}

	
	
	
#else
	for (int i = 0; i < transitions.size(); i++) {
		Element<std::string> t(transitions[i]);

		NodeSet<std::string> targets = getTargetStates(t);
		for (int j = 0; j < targets.size(); j++) {
			if (!isMember(targets[j], statesToEnter)) {
#if VERBOSE
				std::cout << "adding: " << ATTR_CAST(anc, "id") << std::endl;
#endif
				statesToEnter.push_back(targets[j]);
			}
		}
	}

#if VERBOSE
	std::cout << "before addDescendantStatesToEnter: ";
	for (int i = 0; i < statesToEnter.size(); i++) {
		std::cout << ATTR_CAST(statesToEnter[i], "id") << " ";
	}
	std::cout << std::endl;
#endif

	NodeSet<std::string> tmp = statesToEnter;
	for (int i = 0; i < tmp.size(); i++) {
		assert(tmp[i]);
		addDescendantStatesToEnter(tmp[i],statesToEnter,statesForDefaultEntry, defaultHistoryContent);
	}

#if VERBOSE
	std::cout << "after addDescendantStatesToEnter: ";
	for (int i = 0; i < statesToEnter.size(); i++) {
		std::cout << ATTR_CAST(statesToEnter[i], "id") << " ";
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

#if VERBOSE
	std::cout << "after addAncestorStatesToEnter: ";
	for (int i = 0; i < statesToEnter.size(); i++) {
		std::cout << ATTR_CAST(statesToEnter[i], "id") << " ";
	}
	std::cout << std::endl;
#endif
	
#endif
}

Arabica::XPath::NodeSet<std::string> InterpreterRC::getEffectiveTargetStates(const Arabica::DOM::Element<std::string>& transition) {
	NodeSet<std::string> effectiveTargets;
	NodeSet<std::string> targets = getTargetStates(transition);

	for (int j = 0; j < targets.size(); j++) {
		Element<std::string> s = Element<std::string>(targets[j]);
		if (isHistory(s)) {
			if (_historyValue.find(ATTR(s, "id")) != _historyValue.end()) {
				targets.push_back(_historyValue["id"]);
			} else {
				NodeSet<std::string> histTrans = filterChildElements(_nsInfo.xmlNSPrefix + "transition", s);
				// TODO: what if there are many history transitions?
				if (histTrans.size() > 0)
					targets.push_back(getEffectiveTargetStates(Element<std::string>(histTrans[0])));
			}
		} else {
			effectiveTargets.push_back(s);
		}
	}

	return effectiveTargets;
}

void InterpreterRC::computeEntrySet(const Arabica::DOM::Node<std::string>& transition,
                                    NodeSet<std::string>& statesToEnter,
                                    NodeSet<std::string>& statesForDefaultEntry,
                                    std::map<std::string, Arabica::DOM::Node<std::string> > defaultHistoryContent) {
	Arabica::XPath::NodeSet<std::string> transitions;
	transitions.push_back(transition);
	computeEntrySet(transitions, statesToEnter, statesForDefaultEntry, defaultHistoryContent);
}

void InterpreterRC::addDescendantStatesToEnter(const Arabica::DOM::Element<std::string>& state,
        Arabica::XPath::NodeSet<std::string>& statesToEnter,
        Arabica::XPath::NodeSet<std::string>& statesForDefaultEntry,
        std::map<std::string, Arabica::DOM::Node<std::string> > defaultHistoryContent) {

#if VERBOSE
	std::cout << getPadding() << "addDescendantStatesToEnter: " << ATTR(state, "id") << std::endl;
	padding++;
#endif
	
	if (isHistory(state)) {
		
		std::string stateId = ATTR(state, "id");
		if (_historyValue.find(stateId) != _historyValue.end()) {
			const Arabica::XPath::NodeSet<std::string>& historyValue = _historyValue[stateId];
			for (int i = 0; i < historyValue.size(); i++) {
				const Element<std::string>& s = Element<std::string>(historyValue[i]);
				addDescendantStatesToEnter(s,statesToEnter,statesForDefaultEntry, defaultHistoryContent);
				addAncestorStatesToEnter(s, getParentState(s), statesToEnter, statesForDefaultEntry, defaultHistoryContent);
			}
			
		} else {
			NodeSet<std::string> transitions = filterChildElements(_nsInfo.xmlNSPrefix + "transition", state);
			if (transitions.size() > 0) {
				// TODO: what if there are many history transitions?
				defaultHistoryContent[stateId] = transitions[0];
			}
			
			for (int i = 0; i < transitions.size(); i++) {
				NodeSet<std::string> targets = getTargetStates(Element<std::string>(transitions[i]));
				for (int j = 0; j < targets.size(); j++) {
					const Element<std::string>& s = Element<std::string>(targets[i]);
					addDescendantStatesToEnter(s,statesToEnter,statesForDefaultEntry, defaultHistoryContent);
					addAncestorStatesToEnter(s, getParentState(s), statesToEnter, statesForDefaultEntry, defaultHistoryContent);
				}
			}
		}
	} else {
		
		if (!isMember(state, statesToEnter)) { // adding an existing element invalidates old reference
#if VERBOSE
			std::cout << getPadding() << "adding: " << ATTR_CAST(state, "id") << std::endl;
#endif
			statesToEnter.push_back(state);
		}

		if (isCompound(state)) {
			statesForDefaultEntry.push_back(state);

			NodeSet<std::string> targets = getInitialStates(Element<std::string>(state));
			for (int i = 0; i < targets.size(); i++) {
				const Element<std::string>& s = Element<std::string>(targets[i]);
				addDescendantStatesToEnter(s,statesToEnter,statesForDefaultEntry, defaultHistoryContent);
			}

			for (int i = 0; i < targets.size(); i++) {
				const Element<std::string>& s = Element<std::string>(targets[i]);
				addAncestorStatesToEnter(s, state, statesToEnter, statesForDefaultEntry, defaultHistoryContent);
			}
			
		} else if(isParallel(state)) {
			NodeSet<std::string> childStates = getChildStates(state);
			
			for (int i = 0; i < childStates.size(); i++) {
				const Element<std::string>& child = Element<std::string>(childStates[i]);
				
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
	padding--;
}

void InterpreterRC::addAncestorStatesToEnter(const Arabica::DOM::Element<std::string>& state,
        const Arabica::DOM::Element<std::string>& ancestor,
        Arabica::XPath::NodeSet<std::string>& statesToEnter,
        Arabica::XPath::NodeSet<std::string>& statesForDefaultEntry,
        std::map<std::string, Arabica::DOM::Node<std::string> > defaultHistoryContent) {

#if VERBOSE
	std::cout << getPadding() << "addAncestorStatesToEnter: " << ATTR(state, "id") << " - " << ATTR(ancestor, "id")  << std::endl;
	padding++;
#endif
	
	NodeSet<std::string> ancestors = getProperAncestors(state, ancestor);
	for (int i = 0; i < ancestors.size(); i++) {
		const Node<std::string>& anc = ancestors[i];
#if VERBOSE
		std::cout << getPadding() << "adding: " << ATTR_CAST(anc, "id") << std::endl;
#endif
		statesToEnter.push_back(anc);
		if (isParallel(Element<std::string>(anc))) {
			NodeSet<std::string> childStates = getChildStates(anc);
			for (int j = 0; j < childStates.size(); j++) {
				const Element<std::string>& child = Element<std::string>(childStates[j]);
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
	padding--;
}


Arabica::DOM::Node<std::string> InterpreterRC::getTransitionDomain(const Arabica::DOM::Element<std::string>& transition) {
#if 1
	
	NodeSet<std::string> tStates = getEffectiveTargetStates(transition);
	Node<std::string> source = getSourceState(transition);

	if (tStates.size() == 0) {
		return Arabica::DOM::Node<std::string>(); // null
	}
	std::string transitionType = (HAS_ATTR(transition, "type") ? ATTR(transition, "type") : "external");

	if (iequals(transitionType, "internal") && isCompound(Element<std::string>(source))) {
		for (int i = 0; i < tStates.size(); i++) {
			const Node<std::string>& s = tStates[i];
			if (!isDescendant(s, source))
				goto BREAK_LOOP;
		}
		return source;
	}

BREAK_LOOP:
	Arabica::XPath::NodeSet<std::string> states;
	states.push_back(source);
	states.push_back(tStates);
	return findLCCA(states);

#else
	NodeSet<std::string> tStates = getTargetStates(transition);
	Node<std::string> source = getSourceState(transition);

#if VERBOSE
	std::cout << "getTransitionDomain: " << std::endl << transition << std::endl;
#endif

	if (tStates.size() == 0) {
		return Arabica::DOM::Node<std::string>(); // null
	}
	std::string transitionType = (HAS_ATTR(transition, "type") ? ATTR(transition, "type") : "external");

	if (iequals(transitionType, "internal") && isCompound(Element<std::string>(source))) {
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
#endif
}

}