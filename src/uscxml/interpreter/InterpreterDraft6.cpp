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
#include "uscxml/concurrency/DelayedEventQueue.h"

#include <glog/logging.h>
#include "uscxml/UUID.h"
#include "uscxml/DOMUtils.h"

#define VERBOSE 0

namespace uscxml {

using namespace Arabica::XPath;
using namespace Arabica::DOM;

// see: http://www.w3.org/TR/scxml/#AlgorithmforSCXMLInterpretation


Arabica::XPath::NodeSet<std::string> InterpreterDraft6::removeConflictingTransitions(const Arabica::XPath::NodeSet<std::string>& enabledTransitions) {
	Arabica::XPath::NodeSet<std::string> filteredTransitions;
	for (unsigned int i = 0; i < enabledTransitions.size(); i++) {
		Element<std::string> t(enabledTransitions[i]);
		if (!isTargetless(t)) {
			for (unsigned int j = 0; j < filteredTransitions.size(); j++) {
				if (j == i)
					continue;
				Element<std::string> t2(filteredTransitions[j]);
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
bool InterpreterDraft6::isPreemptingTransition(const Element<std::string>& t1, const Element<std::string>& t2) {
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

bool InterpreterDraft6::isCrossingBounds(const Element<std::string>& transition) {
	if (!isTargetless(transition) && !isWithinParallel(transition))
		return true;
	return false;
}

bool InterpreterDraft6::isWithinParallel(const Element<std::string>& transition) {
	if (isTargetless(transition))
		return false;

	if (_transWithinParallel.find(transition) != _transWithinParallel.end())
		return _transWithinParallel[transition];

	Node<std::string> source;
	if (HAS_ATTR(transition, "type") && iequals(ATTR(transition, "type"), "internal")) {
		source = getSourceState(transition);
	} else {
		source = getSourceState(transition).getParentNode();
	}
	NodeSet<std::string> targets = getTargetStates(transition);
	targets.push_back(source);

	Node<std::string> lcpa = findLCPA(targets);
	_transWithinParallel[transition] = lcpa;

	return _transWithinParallel[transition];
}

Node<std::string> InterpreterDraft6::findLCPA(const Arabica::XPath::NodeSet<std::string>& states) {
	Arabica::XPath::NodeSet<std::string> ancestors = getProperAncestors(states[0], Node<std::string>());
	Node<std::string> ancestor;
	for (int i = 0; i < ancestors.size(); i++) {
		if (!isParallel(Element<std::string>(ancestors[i])))
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



void InterpreterDraft6::exitStates(const Arabica::XPath::NodeSet<std::string>& enabledTransitions) {
	NodeSet<std::string> statesToExit;

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
			if (isInternal && allDescendants && isCompound(Element<std::string>(source))) {
				ancestor = source;
			} else {
				NodeSet<std::string> tmpStates;
				tmpStates.push_back(source);
				tmpStates.insert(tmpStates.end(), tStates.begin(), tStates.end());
#if 0
				std::cout << _name << ": tmpStates: ";
				for (int i = 0; i < tmpStates.size(); i++) {
					std::cout << ATTR(tmpStates[i], "id") << ", ";
				}
				std::cout << std::endl;
#endif
				ancestor = findLCCA(tmpStates);
			}
#if 0
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

#if 0
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
					if (isAtomic(Element<std::string>(_configuration[k])) && isDescendant(_configuration[k], statesToExit[i]))
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
				std::cout << ATTR_CAST(historyNodes[i], "id") << ", ";
			}
			std::cout << std::endl;
#endif

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
	// initialize the temporary table for default content in history states
	NodeSet<std::string> defaultHistoryContent;

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
				std::cout << ATTR_CAST(tStates[i], "id") << ", ";
			}
			std::cout << std::endl;
#endif

			Node<std::string> ancestor;
			Node<std::string> source = getSourceState(transition);
#if VERBOSE
			std::cout << _name << ": Source States: " << ATTR_CAST(source, "id") << std::endl;
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
			        isCompound(Element<std::string>(source)) &&
			        allDescendants) {
				ancestor = source;
			} else {
				NodeSet<std::string> tmpStates;
				tmpStates.push_back(source);
				tmpStates.insert(tmpStates.end(), tStates.begin(), tStates.end());

				ancestor = findLCCA(tmpStates);
			}

#if VERBOSE
			std::cout << _name << ": Ancestor: " << ATTR_CAST(ancestor, "id") << std::endl;
#endif

			for (int j = 0; j < tStates.size(); j++) {
				addStatesToEnter(Element<std::string>(tStates[j]), statesToEnter, statesForDefaultEntry, defaultHistoryContent);
			}

#if VERBOSE
			std::cout << _name << ": States to enter: ";
			for (int i = 0; i < statesToEnter.size(); i++) {
				std::cout << LOCALNAME(statesToEnter[i]) << ":" << ATTR_CAST(statesToEnter[i], "id") << ", ";
			}
			std::cout << std::endl;
#endif

			for (int j = 0; j < tStates.size(); j++) {
				NodeSet<std::string> ancestors = getProperAncestors(tStates[j], ancestor);

#if VERBOSE
				std::cout << _name << ": Proper Ancestors of " << ATTR_CAST(tStates[j], "id") << " and " << ATTR_CAST(ancestor, "id") << ": ";
				for (int i = 0; i < ancestors.size(); i++) {
					std::cout << ATTR_CAST(ancestors[i], "id") << ", ";
				}
				std::cout << std::endl;
#endif

				for (int k = 0; k < ancestors.size(); k++) {
					statesToEnter.push_back(ancestors[k]);
					if(isParallel(Element<std::string>(ancestors[k]))) {
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
								addStatesToEnter(Element<std::string>(childs[l]), statesToEnter, statesForDefaultEntry, defaultHistoryContent);
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
		std::cout << ATTR_CAST(statesToEnter[i], "id") << ", ";
	}
	std::cout << std::endl;
#endif

	for (int i = 0; i < statesToEnter.size(); i++) {
		Element<std::string> stateElem = (Element<std::string>)statesToEnter[i];

		// extension for flattened interpreters
		for (unsigned int k = 0; k < statesToEnter.size(); k++) {
			NodeSet<std::string> invokes = filterChildElements(_nsInfo.xmlNSPrefix + "invoke", statesToEnter[k]);
			for (unsigned int j = 0; j < invokes.size(); j++) {
				Element<std::string> invokeElem = Element<std::string>(invokes[j]);
				if (HAS_ATTR(invokeElem, "persist") && DOMUtils::attributeIsTrue(ATTR(invokeElem, "persist"))) {
					invoke(invokeElem);
				}
			}
		}

		USCXML_MONITOR_CALLBACK3(beforeEnteringState, stateElem, (i + 1 < statesToEnter.size()))

		// extension for flattened SCXML documents, we will need an explicit uninvoke element
		NodeSet<std::string> uninvokes = filterChildElements(_nsInfo.xmlNSPrefix + "uninvoke", statesToEnter[i]);
		for (int j = 0; j < uninvokes.size(); j++) {
			Element<std::string> uninvokeElem = (Element<std::string>)uninvokes[j];
			cancelInvoke(uninvokeElem);
		}

		_configuration.push_back(stateElem);
		_statesToInvoke.push_back(stateElem);

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
		}
		// execute onentry executable content
		NodeSet<std::string> onEntryElems = filterChildElements(_nsInfo.xmlNSPrefix + "onEntry", stateElem);
		executeContent(onEntryElems, false);

		USCXML_MONITOR_CALLBACK3(afterEnteringState, stateElem, (i + 1 < statesToEnter.size()))

		if (isMember(stateElem, statesForDefaultEntry)) {
			// execute initial transition content for compound states
			Arabica::XPath::NodeSet<std::string> transitions = _xpath.evaluate("" + _nsInfo.xpathPrefix + "initial/" + _nsInfo.xpathPrefix + "transition", stateElem).asNodeSet();
			for (int j = 0; j < transitions.size(); j++) {
				executeContent(Element<std::string>(transitions[j]));
			}
		}

#if 0
		// not working yet
		if (isMember(stateElem, defaultHistoryContent)) {
			// execute history transition
			Arabica::XPath::NodeSet<std::string> transitions = _xpath.evaluate("" + _nsInfo.xpathPrefix + "history/" + _nsInfo.xpathPrefix + "transition", stateElem).asNodeSet();
			for (int j = 0; j < transitions.size(); j++) {
				executeContent(transitions[j]);
			}
		}
#endif
		if (isFinal(stateElem)) {
			internalDoneSend(stateElem);
			Node<std::string> parent = stateElem.getParentNode();

			if (parent.getNodeType() == Node_base::ELEMENT_NODE &&
			        parent.getParentNode().getNodeType() == Node_base::ELEMENT_NODE &&
			        isParallel(Element<std::string>(parent.getParentNode()))) {
				Element<std::string> grandParent = (Element<std::string>)parent.getParentNode();

				Arabica::XPath::NodeSet<std::string> childs = getChildStates(grandParent);
				bool inFinalState = true;
				for (int j = 0; j < childs.size(); j++) {
					if (!isInFinalState(Element<std::string>(childs[j]))) {
						inFinalState = false;
						break;
					}
				}
				if (inFinalState) {
					internalDoneSend(Element<std::string>(parent));
				}
			}
		}
	}
	for (int i = 0; i < _configuration.size(); i++) {
		Element<std::string> stateElem = (Element<std::string>)_configuration[i];
		if (isFinal(stateElem) && parentIsScxmlState(stateElem)) {
			_topLevelFinalReached = true;
		}
	}
}

void InterpreterDraft6::addStatesToEnter(const Element<std::string>& state,
        Arabica::XPath::NodeSet<std::string>& statesToEnter,
        Arabica::XPath::NodeSet<std::string>& statesForDefaultEntry,
        Arabica::XPath::NodeSet<std::string>& defaultHistoryContent) {
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
				std::cout << ATTR_CAST(historyValue[i], "id") << ", ";
			}
			std::cout << std::endl;
#endif

			for (int i = 0; i < historyValue.size(); i++) {
				addStatesToEnter(Element<std::string>(historyValue[i]), statesToEnter, statesForDefaultEntry, defaultHistoryContent);
				NodeSet<std::string> ancestors = getProperAncestors(historyValue[i], state);

#if VERBOSE
				std::cout << "Proper Ancestors: ";
				for (int i = 0; i < ancestors.size(); i++) {
					std::cout << ATTR_CAST(ancestors[i], "id") << ", ";
				}
				std::cout << std::endl;
#endif

				for (int j = 0; j < ancestors.size(); j++) {
					statesToEnter.push_back(ancestors[j]);
				}
			}
		} else {
			defaultHistoryContent.push_back(getParentState(state));
			NodeSet<std::string> transitions = filterChildElements(_nsInfo.xmlNSPrefix + "transition", state);
			for (int i = 0; i < transitions.size(); i++) {
				NodeSet<std::string> targets = getTargetStates(Element<std::string>(transitions[i]));
				for (int j = 0; j < targets.size(); j++) {
					addStatesToEnter(Element<std::string>(targets[j]), statesToEnter, statesForDefaultEntry, defaultHistoryContent);

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
				addStatesToEnter(Element<std::string>(tStates[i]), statesToEnter, statesForDefaultEntry, defaultHistoryContent);
			}

			//			addStatesToEnter(getInitialState(state), statesToEnter, statesForDefaultEntry);
			//      NodeSet<std::string> tStates = getTargetStates(getInitialState(state));

		} else if(isParallel(state)) {
			NodeSet<std::string> childStates = getChildStates(state);
			for (int i = 0; i < childStates.size(); i++) {
				addStatesToEnter(Element<std::string>(childStates[i]), statesToEnter, statesForDefaultEntry, defaultHistoryContent);
			}
		}
	}
}

void InterpreterDraft6::handleDOMEvent(Arabica::DOM::Events::Event<std::string>& event) {
	InterpreterImpl::handleDOMEvent(event);

	// remove modified states from cache
	if (event.getType().compare("DOMAttrModified") == 0) // we do not care about attributes
		return;
	Node<std::string> target = Arabica::DOM::Node<std::string>(event.getTarget());
	NodeSet<std::string> transitions = InterpreterImpl::filterChildElements(_nsInfo.xmlNSPrefix + "transition", target);
	for (int i = 0; i < transitions.size(); i++) {
		const Element<std::string> transElem = Element<std::string>(transitions[i]);
		if (_transWithinParallel.find(transElem) != _transWithinParallel.end())
			_transWithinParallel.erase(transElem);
	}
}


}