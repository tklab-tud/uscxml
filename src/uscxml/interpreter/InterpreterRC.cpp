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
#include "uscxml/dom/DOMUtils.h"

#define VERBOSE 0
#define VERBOSE_STATE_SELECTION 0
#define VERBOSE_FIND_LCCA 0

namespace uscxml {

using namespace Arabica::XPath;
using namespace Arabica::DOM;

#if 1
size_t padding = 0;
std::string getPadding() {
	std::string pad = "";
	for (size_t i = 0; i < padding; i++) {
		pad += "  ";
	}
	return pad;
}
#endif

Arabica::XPath::NodeSet<std::string> InterpreterRC::removeConflictingTransitions(const Arabica::XPath::NodeSet<std::string>& enabledTransitions) {
	Arabica::XPath::NodeSet<std::string> filteredTransitions;
	for (unsigned int i = 0; i < enabledTransitions.size(); i++) {
		Element<std::string> t1(enabledTransitions[i]);
		bool t1Preempted = false;
		Arabica::XPath::NodeSet<std::string> transitionsToRemove;

		for (unsigned int j = 0; j < filteredTransitions.size(); j++) {
			Element<std::string> t2(filteredTransitions[j]);
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
			// remove transitionsToRemove from DOMUtils::filteredTransitions
			std::list<Node<std::string> > tmp;
			for (size_t i = 0; i < filteredTransitions.size(); i++) {
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

#if VERBOSE_STATE_SELECTION
	std::cout << "exitStates: ";
	for (size_t i = 0; i < statesToExit.size(); i++) {
		std::cout << ATTR_CAST(statesToExit[i], "id") << " ";
	}
	std::cout << std::endl;
#endif

	// remove statesToExit from _statesToInvoke
	std::list<Node<std::string> > tmp;
	for (size_t i = 0; i < _statesToInvoke.size(); i++) {
		if (!isMember(_statesToInvoke[i], statesToExit)) {
			tmp.push_back(_statesToInvoke[i]);
		}
	}
	_statesToInvoke = NodeSet<std::string>();
	_statesToInvoke.insert(_statesToInvoke.end(), tmp.begin(), tmp.end());

	statesToExit.forward(false);
	statesToExit.sort();


	for (size_t i = 0; i < statesToExit.size(); i++) {
		NodeSet<std::string> histories = DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "history", statesToExit[i]);
		for (size_t j = 0; j < histories.size(); j++) {
			Element<std::string> historyElem = (Element<std::string>)histories[j];
			std::string historyType = (historyElem.hasAttribute("type") ? historyElem.getAttribute("type") : "shallow");
			NodeSet<std::string> historyNodes;
			for (size_t k = 0; k < _configuration.size(); k++) {
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

	for (size_t i = 0; i < statesToExit.size(); i++) {
		USCXML_MONITOR_CALLBACK3(beforeExitingState, Element<std::string>(statesToExit[i]), (i + 1 < statesToExit.size()))

		NodeSet<std::string> onExits = DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "onExit", statesToExit[i]);
		for (size_t j = 0; j < onExits.size(); j++) {
			Element<std::string> onExitElem = (Element<std::string>)onExits[j];
			executeContent(onExitElem);
		}

		USCXML_MONITOR_CALLBACK3(afterExitingState, Element<std::string>(statesToExit[i]), (i + 1 < statesToExit.size()))

		NodeSet<std::string> invokes = DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "invoke", statesToExit[i]);
		for (size_t j = 0; j < invokes.size(); j++) {
			Element<std::string> invokeElem = (Element<std::string>)invokes[j];
			if (HAS_ATTR(invokeElem, "persist") && stringIsTrue(ATTR(invokeElem, "persist"))) {
			} else {
				cancelInvoke(invokeElem);
			}
		}

		// remove statesToExit[i] from _configuration - test409
		tmp.clear();
		for (size_t j = 0; j < _configuration.size(); j++) {
			if (_configuration[j] != statesToExit[i]) {
				tmp.push_back(_configuration[j]);
			}
		}
		_configuration = NodeSet<std::string>();
		_configuration.insert(_configuration.end(), tmp.begin(), tmp.end());
	}
}

/*
function computeExitSet(transitions)
   statesToExit = new OrderedSet
     for t in transitions:
       if(t.target):
          domain = getTransitionDomain(t)
          for s in configuration:
             if isDescendant(s,domain):
               statesToExit.add(s)
   return statesToExit
*/
Arabica::XPath::NodeSet<std::string> InterpreterRC::computeExitSet(const Arabica::XPath::NodeSet<std::string>& transitions) {

	NodeSet<std::string> statesToExit;
	for (unsigned int i = 0; i < transitions.size(); i++) {
		Element<std::string> t(transitions[i]);
		if (!isTargetless(t)) {
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
	}
#if VERBOSE
	std::cout << "computeExitSet: ";
	for (size_t i = 0; i < statesToExit.size(); i++) {
		std::cout << ATTR_CAST(statesToExit[i], "id") << " ";
	}
	std::cout << std::endl;
#endif

	return statesToExit;
}

Arabica::XPath::NodeSet<std::string> InterpreterRC::computeExitSet(const Arabica::DOM::Node<std::string>& transition) {
//	if (_exitSet.find(transition) != _exitSet.end()) // speed up removeConflicting
//		return _exitSet[transition];

	Arabica::XPath::NodeSet<std::string> transitions;
	transitions.push_back(transition);

	Arabica::XPath::NodeSet<std::string> exitSet = computeExitSet(transitions);
	//_exitSet[transition] = exitSet;

#if 0
	std::cerr << "Exit set for transition '" << transition << "': " << std::endl;
	for (size_t i = 0; i < exitSet.size(); i++) {
		std::cerr << ATTR_CAST(exitSet[i], "id") << std::endl << "----" << std::endl;
	}
	std::cerr << std::endl;
#endif
	return exitSet;
}

void InterpreterRC::enterStates(const Arabica::XPath::NodeSet<std::string>& enabledTransitions) {
	NodeSet<std::string> statesToEnter;
	NodeSet<std::string> statesForDefaultEntry;
	// initialize the temporary table for default content in history states
	std::map<std::string, Arabica::DOM::Node<std::string> > defaultHistoryContent;

	computeEntrySet(enabledTransitions, statesToEnter, statesForDefaultEntry, defaultHistoryContent);
	statesToEnter.to_document_order();

#if VERBOSE_STATE_SELECTION
	std::cout << "enterStates: ";
	for (size_t i = 0; i < statesToEnter.size(); i++) {
		std::cout << ATTR_CAST(statesToEnter[i], "id") << " ";
	}
	std::cout << std::endl;
#endif

	for (size_t i = 0; i < statesToEnter.size(); i++) {
		Element<std::string> s = (Element<std::string>)statesToEnter[i];

		USCXML_MONITOR_CALLBACK3(beforeEnteringState, s, i + 1 < statesToEnter.size())

		_configuration.push_back(s);
		_statesToInvoke.push_back(s);

		if (_binding == LATE && !isMember(s, _alreadyEntered)) {
			NodeSet<std::string> dataModelElems = DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "datamodel", s);
			if(dataModelElems.size() > 0 && _dataModel) {
				Arabica::XPath::NodeSet<std::string> dataElems = DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "data", dataModelElems[0]);
				for (size_t j = 0; j < dataElems.size(); j++) {
					if (dataElems[j].getNodeType() == Node_base::ELEMENT_NODE)
						initializeData(Element<std::string>(dataElems[j]));
				}
			}
			_alreadyEntered.push_back(s);
		}
		// execute onentry executable content
		NodeSet<std::string> onEntryElems = DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "onEntry", s);
		executeContent(onEntryElems, false);

		if (isMember(s, statesForDefaultEntry)) {
			// execute initial transition content for compound states
			Arabica::XPath::NodeSet<std::string> transitions = _xpath.evaluate("" + _nsInfo.xpathPrefix + "initial/" + _nsInfo.xpathPrefix + "transition", s).asNodeSet();
			if (transitions.size() > 0) {
				executeContent(transitions);
			}
		}

		USCXML_MONITOR_CALLBACK3(afterEnteringState, s, i + 1 < statesToEnter.size())

		if (HAS_ATTR(_scxml, "flat") && stringIsTrue(ATTR(_scxml, "flat"))) {
			// extension for flattened interpreters
			NodeSet<std::string> invokes = DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "invoke", s);
			for (unsigned int j = 0; j < invokes.size(); j++) {
				Element<std::string> invokeElem = Element<std::string>(invokes[j]);
				if (HAS_ATTR(invokeElem, "persist") && stringIsTrue(ATTR(invokeElem, "persist"))) {
					invoke(invokeElem);
				}
			}

			// extension for flattened SCXML documents, we will need an explicit uninvoke element
			NodeSet<std::string> uninvokes = DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "uninvoke", s);
			for (size_t j = 0; j < uninvokes.size(); j++) {
				Element<std::string> uninvokeElem = (Element<std::string>)uninvokes[j];
				cancelInvoke(uninvokeElem);
			}
		}

//		std::cout << "HIST?: " << ATTR(s, "id") << std::endl;
		if (defaultHistoryContent.find(ATTR(s, "id")) != defaultHistoryContent.end()) {
			executeContent(Element<std::string>(defaultHistoryContent[ATTR(s, "id")]));
		}

		if (isFinal(s)) {
			Element<std::string> parent = (Element<std::string>)s.getParentNode();

			Arabica::DOM::Element<std::string> doneData;
			Arabica::XPath::NodeSet<std::string> doneDatas = DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "donedata", s);
			if (doneDatas.size() > 0) {
				// only process first donedata element
				doneData = Element<std::string>(doneDatas[0]);
			}

			if (parentIsScxmlState(s)) {
				_topLevelFinalReached = true;
			} else {
				internalDoneSend(parent, doneData);
				Element<std::string> grandParent = (Element<std::string>)parent.getParentNode();

//				internalDoneSend(parent, Arabica::DOM::Element<std::string>());

				if (isParallel(grandParent)) {
					Arabica::XPath::NodeSet<std::string> childs = getChildStates(grandParent);
					bool inFinalState = true;
					for (size_t j = 0; j < childs.size(); j++) {
						if (!isInFinalState(Element<std::string>(childs[j]))) {
							inFinalState = false;
							break;
						}
					}
					if (inFinalState) {
						internalDoneSend(grandParent, Arabica::DOM::Element<std::string>());
					}
				}
			}
		}
	}
}

/*
procedure computeEntrySet(transitions, statesToEnter, statesForDefaultEntry, defaultHistoryContent)
   for t in transitions:
       for s in t.target:
           addDescendantStatesToEnter(s,statesToEnter,statesForDefaultEntry, defaultHistoryContent)
       ancestor = getTransitionDomain(t)
       for s in getEffectiveTargetStates(t)):
           addAncestorStatesToEnter(s, ancestor, statesToEnter, statesForDefaultEntry, defaultHistoryContent)
*/

void InterpreterRC::computeEntrySet(const Arabica::XPath::NodeSet<std::string>& transitions,
                                    NodeSet<std::string>& statesToEnter,
                                    NodeSet<std::string>& statesForDefaultEntry,
                                    std::map<std::string, Arabica::DOM::Node<std::string> >& defaultHistoryContent) {

	// add all descendants in a dedicated first step
	for (size_t i = 0; i < transitions.size(); i++) {
		Element<std::string> t(transitions[i]);

		NodeSet<std::string> targets = getTargetStates(t);
		for (size_t j = 0; j < targets.size(); j++) {
			Element<std::string> s = Element<std::string>(targets[j]);
			addDescendantStatesToEnter(s, statesToEnter, statesForDefaultEntry, defaultHistoryContent);
		}
	}

	// only now add the ancestors
	for (size_t i = 0; i < transitions.size(); i++) {
		Element<std::string> t(transitions[i]);
		Element<std::string> ancestor = Element<std::string>(getTransitionDomain(t));
		NodeSet<std::string> effectiveTargetStates = getEffectiveTargetStates(t);

		for (size_t j = 0; j < effectiveTargetStates.size(); j++) {
			Element<std::string> s = Element<std::string>(effectiveTargetStates[j]);
			addAncestorStatesToEnter(s, ancestor, statesToEnter, statesForDefaultEntry, defaultHistoryContent);
		}

	}
}

/*
function getEffectiveTargetStates(transition)
    effectiveTargets = new OrderedSet()
    for s in transition.target
        if isHistoryState(s):
            if historyValue[s.id]:
                effectiveTargets.union(historyValue[s.id])
            else:
                effectiveTargets.union(getEffectiveTargetStates(s.transition))
       else:
           effectiveTargets.add(s)
    return effectiveTargets
*/

Arabica::XPath::NodeSet<std::string> InterpreterRC::getEffectiveTargetStates(const Arabica::DOM::Element<std::string>& transition) {
	NodeSet<std::string> effectiveTargets;

	NodeSet<std::string> targets;
	if (isState(transition)) {
		targets = getInitialStates(transition);
		return targets;
	} else {
		targets = getTargetStates(transition);
	}

	for (size_t j = 0; j < targets.size(); j++) {
		Element<std::string> s = Element<std::string>(targets[j]);
		if (isHistory(s)) {
			if (_historyValue.find(ATTR(s, "id")) != _historyValue.end()) {
				targets.push_back(_historyValue[ATTR(s, "id")]);
			} else {
				NodeSet<std::string> histTrans = DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "transition", s);
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
                                    std::map<std::string, Arabica::DOM::Node<std::string> >& defaultHistoryContent) {
	Arabica::XPath::NodeSet<std::string> transitions;
	transitions.push_back(transition);
	computeEntrySet(transitions, statesToEnter, statesForDefaultEntry, defaultHistoryContent);
}


/*
procedure addDescendantStatesToEnter(state,statesToEnter,statesForDefaultEntry, defaultHistoryContent):
    if isHistoryState(state):
        if historyValue[state.id]:
            for s in historyValue[state.id]:
                addDescendantStatesToEnter(s,statesToEnter,statesForDefaultEntry, defaultHistoryContent)
                addAncestorStatesToEnter(s, state.parent, statesToEnter, statesForDefaultEntry, defaultHistoryContent)
        else:
            defaultHistoryContent[state.parent.id] = state.transition.content
            for s in state.transition.target:
                addDescendantStatesToEnter(s,statesToEnter,statesForDefaultEntry, defaultHistoryContent)
                addAncestorStatesToEnter(s, state.parent, statesToEnter, statesForDefaultEntry, defaultHistoryContent)
    else:
        statesToEnter.add(state)
        if isCompoundState(state):
            statesForDefaultEntry.add(state)
            for s in getEffectiveTargetStates(state.initial.transition):
                addDescendantStatesToEnter(s,statesToEnter,statesForDefaultEntry, defaultHistoryContent)
                addAncestorStatesToEnter(s, state, statesToEnter, statesForDefaultEntry, defaultHistoryContent)
        else:
            if isParallelState(state):
                 for child in getChildStates(state):
                     if not statesToEnter.some(lambda s: isDescendant(s,child)):
                          addDescendantStatesToEnter(child,statesToEnter,statesForDefaultEntry, defaultHistoryContent)
*/
void InterpreterRC::addDescendantStatesToEnter(const Arabica::DOM::Element<std::string>& state,
        Arabica::XPath::NodeSet<std::string>& statesToEnter,
        Arabica::XPath::NodeSet<std::string>& statesForDefaultEntry,
        std::map<std::string, Arabica::DOM::Node<std::string> >& defaultHistoryContent) {

#if VERBOSE_STATE_SELECTION
	std::cout << getPadding() << "addDescendantStatesToEnter: " << ATTR(state, "id") << std::endl;
	padding++;
#endif

	if (isHistory(state)) {

		/*
		if historyValue[state.id]:
		    for s in historyValue[state.id]:
		        addDescendantStatesToEnter(s,statesToEnter,statesForDefaultEntry, defaultHistoryContent)
		        addAncestorStatesToEnter(s, state.parent, statesToEnter, statesForDefaultEntry, defaultHistoryContent)
		else:
		    defaultHistoryContent[state.parent.id] = state.transition.content
		    for s in state.transition.target:
		        addDescendantStatesToEnter(s,statesToEnter,statesForDefaultEntry, defaultHistoryContent)
		        addAncestorStatesToEnter(s, state.parent, statesToEnter, statesForDefaultEntry, defaultHistoryContent)
		 */
		std::string stateId = ATTR(state, "id");
		if (_historyValue.find(stateId) != _historyValue.end()) {
			const Arabica::XPath::NodeSet<std::string>& historyValue = _historyValue[stateId];
			for (size_t i = 0; i < historyValue.size(); i++) {
				const Element<std::string>& s = Element<std::string>(historyValue[i]);
				addDescendantStatesToEnter(s,statesToEnter,statesForDefaultEntry, defaultHistoryContent);
				addAncestorStatesToEnter(s, getParentState(s), statesToEnter, statesForDefaultEntry, defaultHistoryContent);
			}

		} else {
			NodeSet<std::string> transitions = DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "transition", state);
			if (transitions.size() > 0) {
				// TODO: what if there are many history transitions?
//				std::cout << "HIST: " << ATTR_CAST(getParentState(state), "id") << std::endl;
				defaultHistoryContent[ATTR_CAST(getParentState(state), "id")] = transitions[0];
			}

			for (size_t i = 0; i < transitions.size(); i++) {
				NodeSet<std::string> targets = getTargetStates(Element<std::string>(transitions[i]));
				for (size_t j = 0; j < targets.size(); j++) {
					const Element<std::string>& s = Element<std::string>(targets[i]);
					addDescendantStatesToEnter(s,statesToEnter,statesForDefaultEntry, defaultHistoryContent);
					addAncestorStatesToEnter(s, getParentState(s), statesToEnter, statesForDefaultEntry, defaultHistoryContent);
				}
			}
		}
	} else {
		/*
		statesToEnter.add(state)
		if isCompoundState(state):
		    statesForDefaultEntry.add(state)
		    for s in getEffectiveTargetStates(state.initial.transition):
		        addDescendantStatesToEnter(s,statesToEnter,statesForDefaultEntry, defaultHistoryContent)
		        addAncestorStatesToEnter(s, state, statesToEnter, statesForDefaultEntry, defaultHistoryContent)
		else:
		    if isParallelState(state):
		         for child in getChildStates(state):
		             if not statesToEnter.some(lambda s: isDescendant(s,child)):
		                  addDescendantStatesToEnter(child,statesToEnter,statesForDefaultEntry, defaultHistoryContent)
		*/

		if (!isMember(state, statesToEnter)) { // adding an existing element invalidates old reference
#if VERBOSE_STATE_SELECTION
			std::cout << getPadding() << "adding: " << ATTR_CAST(state, "id") << std::endl;
#endif
			statesToEnter.push_back(state);
		}

		if (isCompound(state)) {
			statesForDefaultEntry.push_back(state);

			// test 579 - initial leads to history still fails
			NodeSet<std::string> targets = getEffectiveTargetStates(Element<std::string>(state));
			for (size_t i = 0; i < targets.size(); i++) {
				const Element<std::string>& s = Element<std::string>(targets[i]);
				addDescendantStatesToEnter(s, statesToEnter, statesForDefaultEntry, defaultHistoryContent);
			}

			for (size_t i = 0; i < targets.size(); i++) {
				const Element<std::string>& s = Element<std::string>(targets[i]);
				addAncestorStatesToEnter(s, state, statesToEnter, statesForDefaultEntry, defaultHistoryContent);
			}

		} else if(isParallel(state)) {
			NodeSet<std::string> childStates = getChildStates(state);

			for (size_t i = 0; i < childStates.size(); i++) {
				const Element<std::string>& child = Element<std::string>(childStates[i]);

				for (size_t j = 0; j < statesToEnter.size(); j++) {
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

/*
procedure addAncestorStatesToEnter(state, ancestor, statesToEnter, statesForDefaultEntry, defaultHistoryContent)
   for anc in getProperAncestors(state,ancestor):
       statesToEnter.add(anc)
       if isParallelState(anc):
           for child in getChildStates(anc):
               if not statesToEnter.some(lambda s: isDescendant(s,child)):
                  addDescendantStatesToEnter(child,statesToEnter,statesForDefaultEntry, defaultHistoryContent)
*/
void InterpreterRC::addAncestorStatesToEnter(const Arabica::DOM::Element<std::string>& state,
        const Arabica::DOM::Element<std::string>& ancestor,
        Arabica::XPath::NodeSet<std::string>& statesToEnter,
        Arabica::XPath::NodeSet<std::string>& statesForDefaultEntry,
        std::map<std::string, Arabica::DOM::Node<std::string> >& defaultHistoryContent) {

#if VERBOSE_STATE_SELECTION
	std::cout << getPadding() << "addAncestorStatesToEnter: " << ATTR(state, "id") << " - " << ATTR(ancestor, "id")  << std::endl;
	padding++;
#endif

	NodeSet<std::string> ancestors = getProperAncestors(state, ancestor);
	for (size_t i = 0; i < ancestors.size(); i++) {
		const Node<std::string>& anc = ancestors[i];
#if VERBOSE_STATE_SELECTION
		std::cout << getPadding() << "adding: " << ATTR_CAST(anc, "id") << std::endl;
#endif

		statesToEnter.push_back(anc);

		if (isParallel(Element<std::string>(anc))) {
			NodeSet<std::string> childStates = getChildStates(anc);
			for (size_t j = 0; j < childStates.size(); j++) {
				const Element<std::string>& child = Element<std::string>(childStates[j]);
				for (size_t k = 0; k < statesToEnter.size(); k++) {
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

/*
function getTransitionDomain(t)
  tstates = getEffectiveTargetStates(t)
  if not tstates:
      return null
  elif t.type == "internal" and isCompoundState(t.source) and tstates.every(lambda s: isDescendant(s,t.source)):
      return t.source
  else:
      return findLCCA([t.source].append(tstates))
*/
Arabica::DOM::Node<std::string> InterpreterRC::getTransitionDomain(const Arabica::DOM::Element<std::string>& transition) {
	NodeSet<std::string> tStates = getEffectiveTargetStates(transition);
	if (tStates.size() == 0) {
		return Arabica::DOM::Node<std::string>(); // null
	}
	std::string transitionType = (HAS_ATTR(transition, "type") ? ATTR(transition, "type") : "external");
	Node<std::string> source = getSourceState(transition);

	if (iequals(transitionType, "internal") && isCompound(Element<std::string>(source))) {
		for (size_t i = 0; i < tStates.size(); i++) {
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
}

void InterpreterRC::handleDOMEvent(Arabica::DOM::Events::Event<std::string>& event) {
	InterpreterImpl::handleDOMEvent(event);

	if (event.getType().compare("DOMAttrModified") == 0) // we do not care about attributes
		return;

//	Node<std::string> target = Arabica::DOM::Node<std::string>(event.getTarget());
//	NodeSet<std::string> transitions = DOMUtils::DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "transition", target, true);
//	if (transitions.size() > 0)
	_exitSet.clear();

}
}