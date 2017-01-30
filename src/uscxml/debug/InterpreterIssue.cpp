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

#include <string>

#include "InterpreterIssue.h"
#include "uscxml/util/DOM.h"
#include "uscxml/util/String.h"
#include "uscxml/util/Predicates.h"
#include "uscxml/interpreter/InterpreterImpl.h"
#include "uscxml/plugins/Factory.h"

#include <xercesc/dom/DOMDocument.hpp>

using namespace XERCESC_NS;

namespace uscxml {

InterpreterIssue::InterpreterIssue(const std::string& msg, DOMNode* node, IssueSeverity severity, const std::string& specRef) : message(msg), node(node), severity(severity), specRef(specRef) {
	if (node)
		xPath = DOMUtils::xPathForNode(node);
}

// find all elements in the SCXML namespace in one traversal
void assembleNodeSets(const std::string nsPrefix, DOMElement* node, std::map<std::string, std::list<DOMElement*> >& sets) {
	for (auto childElem = node->getFirstElementChild(); childElem; childElem = childElem->getNextElementSibling()) {

		if (TAGNAME(childElem).find(nsPrefix) == 0) {
			// correct namespace, insert via localname
			sets[LOCALNAME(childElem)].push_back(static_cast<DOMElement*>(childElem));
		}
		assembleNodeSets(nsPrefix, childElem, sets);
	}
}

std::list<std::set<const DOMElement* > > getAllConfigurations(const DOMElement* root) {
	std::list<std::set<const DOMElement* > > allConfigurations;
	std::string nsPrefix = X(root->getPrefix());
	std::string localName = X(root->getLocalName());
	bool isAtomic = true;

//	std::cout << *root;

	for (auto childElem = root->getFirstElementChild(); childElem; childElem = childElem->getNextElementSibling()) {
//		std::cout << *childElem;

		if (XMLString::compareIString(childElem->getTagName(), X(nsPrefix + "state")) == 0 ||
		        XMLString::compareIString(childElem->getTagName(), X(nsPrefix + "parallel")) == 0 ||
		        XMLString::compareIString(childElem->getTagName(), X(nsPrefix + "final")) == 0) {
			// nested child state
			std::list<std::set<const DOMElement*> > nestedConfigurations = getAllConfigurations(childElem);
			isAtomic = false;
			if (localName == "parallel" && allConfigurations.size() > 0) {
				// for every nested configuration, every new nested is valid
				std::list<std::set<const DOMElement*> > combinedConfigurations;
				for (auto existIter = allConfigurations.begin(); existIter != allConfigurations.end(); existIter++) {
					std::set<const DOMElement*> existingConfig = *existIter;

					for (auto newIter = nestedConfigurations.begin(); newIter != nestedConfigurations.end(); newIter++) {

						std::set<const DOMElement*> newConfig = *newIter;
						std::set<const DOMElement*> combinedSet;
						combinedSet.insert(existingConfig.begin(), existingConfig.end());
						combinedSet.insert(newConfig.begin(), newConfig.end());

						combinedConfigurations.push_back(combinedSet);
					}
				}
				allConfigurations = combinedConfigurations;
			} else {
				// just add nested configurations and this
				for (auto newIter = nestedConfigurations.begin(); newIter != nestedConfigurations.end(); newIter++) {
					std::set<const DOMElement*> newConfig = *newIter;
					if (localName != "scxml")
						newConfig.insert(root);
					allConfigurations.push_back(newConfig);
				}
			}
		}
	}

	if (isAtomic) {
		std::set<const DOMElement*> soleConfig;
		soleConfig.insert(root);
		allConfigurations.push_back(soleConfig);
	}
	return allConfigurations;

}

/**
 * Can the given states ever appear in an active configuration?
 */
bool hasLegalCompletion(const std::list<DOMElement*>& states) {
	if (states.size() < 2)
		return true;

	// iterate every pair
	for (auto outer = states.begin(); outer != states.end(); outer++) {
		DOMElement* s1 = *outer;
		for (auto inner = outer; inner != states.end(); inner++) {
			if (inner == outer)
				continue;

			DOMElement* s2 = *inner;
			DOMNode* parent;

			// ok to be directly ancestorally related
			if (DOMUtils::isDescendant(s1, s2) || DOMUtils::isDescendant(s2, s1))
				goto NEXT_PAIR;

			// find least common ancestor
			parent = s1->getParentNode();
			while(parent && parent->getNodeType() == DOMNode::ELEMENT_NODE) {
				if (DOMUtils::isDescendant(s2, parent)) {
					if (isParallel(static_cast<DOMElement*>(parent)))
						goto NEXT_PAIR;
				}
				parent = parent->getParentNode();
			}

			return false;
NEXT_PAIR:
			;
		}
	}
	return true;
}

std::list<InterpreterIssue> InterpreterIssue::forInterpreter(InterpreterImpl* interpreter) {
	// some things we need to prepare first
	if (interpreter->_factory == NULL)
		interpreter->_factory = Factory::getInstance();
	interpreter->setupDOM();

	std::list<InterpreterIssue> issues;

	if (!interpreter->_scxml) {
		InterpreterIssue issue("No SCXML element to be found", NULL, InterpreterIssue::USCXML_ISSUE_FATAL);
		issues.push_back(issue);
		return issues;
	}

	std::map<std::string, DOMElement* > seenStates;

	// get some aliases
	DOMElement* _scxml = interpreter->_scxml;
	Factory* _factory = interpreter->_factory;
	DataModel& _dataModel = interpreter->_dataModel;
	std::string xmlNSPrefix = interpreter->_xmlPrefix;

	std::map<std::string, std::list<DOMElement*> > nodeSets;
	assembleNodeSets(xmlNSPrefix, _scxml, nodeSets);


	std::list<DOMElement*> scxmls = nodeSets["scxml"];
	scxmls.push_back(_scxml);

	std::list<XERCESC_NS::DOMElement*> reachable = getReachableStates(_scxml);

	std::list<DOMElement*>& states = nodeSets["state"];
	std::list<DOMElement*>& parallels = nodeSets["parallel"];
	std::list<DOMElement*>& transitions = nodeSets["transition"];
	std::list<DOMElement*>& initials = nodeSets["initial"];
	std::list<DOMElement*>& finals = nodeSets["final"];
	std::list<DOMElement*>& onEntries = nodeSets["onentry"];
	std::list<DOMElement*>& onExits = nodeSets["onexit"];
	std::list<DOMElement*>& histories = nodeSets["history"];

	std::list<DOMElement*>& raises = nodeSets["raise"];
	std::list<DOMElement*>& ifs = nodeSets["if"];
	std::list<DOMElement*>& elseIfs = nodeSets["elseif"];
	std::list<DOMElement*>& elses = nodeSets["else"];
	std::list<DOMElement*>& foreachs = nodeSets["foreach"];
	std::list<DOMElement*>& logs = nodeSets["log"];

	std::list<DOMElement*>& dataModels = nodeSets["datamodel"];
	std::list<DOMElement*>& datas = nodeSets["data"];
	std::list<DOMElement*>& assigns = nodeSets["assign"];
	std::list<DOMElement*>& doneDatas = nodeSets["donedata"];
	std::list<DOMElement*>& contents = nodeSets["content"];
	std::list<DOMElement*>& params = nodeSets["param"];
	std::list<DOMElement*>& scripts = nodeSets["script"];

	std::list<DOMElement*>& sends = nodeSets["send"];
	std::list<DOMElement*>& cancels = nodeSets["cancel"];
	std::list<DOMElement*>& invokes = nodeSets["invoke"];
	std::list<DOMElement*>& finalizes = nodeSets["finalize"];

	std::list<DOMElement*> allStates;
	allStates.insert(allStates.end(), states.begin(), states.end());
	allStates.insert(allStates.end(), parallels.begin(), parallels.end());
	allStates.insert(allStates.end(), histories.begin(), histories.end());
	allStates.insert(allStates.end(), finals.begin(), finals.end());

	std::list<DOMElement*> allExecContents;
	allExecContents.insert(allExecContents.end(), raises.begin(), raises.end());
	allExecContents.insert(allExecContents.end(), ifs.begin(), ifs.end());
	allExecContents.insert(allExecContents.end(), elseIfs.begin(), elseIfs.end());
	allExecContents.insert(allExecContents.end(), elses.begin(), elses.end());
	allExecContents.insert(allExecContents.end(), foreachs.begin(), foreachs.end());
	allExecContents.insert(allExecContents.end(), logs.begin(), logs.end());
	allExecContents.insert(allExecContents.end(), sends.begin(), sends.end());
	allExecContents.insert(allExecContents.end(), assigns.begin(), assigns.end());
	allExecContents.insert(allExecContents.end(), scripts.begin(), scripts.end());
	allExecContents.insert(allExecContents.end(), cancels.begin(), cancels.end());

	std::list<DOMElement*> allElements;
	allElements.insert(allElements.end(), scxmls.begin(), scxmls.end());
	allElements.insert(allElements.end(), allStates.begin(), allStates.end());
	allElements.insert(allElements.end(), allExecContents.begin(), allExecContents.end());
	allElements.insert(allElements.end(), transitions.begin(), transitions.end());
	allElements.insert(allElements.end(), initials.begin(), initials.end());
	allElements.insert(allElements.end(), onEntries.begin(), onEntries.end());
	allElements.insert(allElements.end(), onExits.begin(), onExits.end());
	allElements.insert(allElements.end(), dataModels.begin(), dataModels.end());
	allElements.insert(allElements.end(), datas.begin(), datas.end());
	allElements.insert(allElements.end(), doneDatas.begin(), doneDatas.end());
	allElements.insert(allElements.end(), contents.begin(), contents.end());
	allElements.insert(allElements.end(), params.begin(), params.end());
	allElements.insert(allElements.end(), invokes.begin(), invokes.end());
	allElements.insert(allElements.end(), finalizes.begin(), finalizes.end());


	std::set<std::string> execContentSet;
	execContentSet.insert("if");
	execContentSet.insert("elseif");
	execContentSet.insert("else");
	execContentSet.insert("foreach");
	execContentSet.insert("raise");
	execContentSet.insert("send");
	execContentSet.insert("cancel");
	execContentSet.insert("assign");
	execContentSet.insert("script");
	execContentSet.insert("log");

	// required attributes per standard
	std::map<std::string, std::set<std::string> > reqAttr;
	reqAttr["scxml"].insert("xmlns");
	reqAttr["scxml"].insert("version");
	reqAttr["raise"].insert("event");
	reqAttr["if"].insert("cond");
	reqAttr["elseif"].insert("cond");
	reqAttr["foreach"].insert("array");
	reqAttr["foreach"].insert("item");
	reqAttr["data"].insert("id");
	reqAttr["assign"].insert("location");
	reqAttr["param"].insert("name");

	// these are the valid children for elements in the SCXML namespace as per specification
	std::map<std::string, std::set<std::string> > validChildren;
	validChildren["scxml"].insert("state");
	validChildren["scxml"].insert("parallel");
	validChildren["scxml"].insert("final");
	validChildren["scxml"].insert("datamodel");
	validChildren["scxml"].insert("script");

	validChildren["state"].insert("onentry");
	validChildren["state"].insert("onexit");
	validChildren["state"].insert("transition");
	validChildren["state"].insert("state");
	validChildren["state"].insert("parallel");
	validChildren["state"].insert("history");
	validChildren["state"].insert("datamodel");
	validChildren["state"].insert("invoke");
	validChildren["state"].insert("initial");
	validChildren["state"].insert("final");

	validChildren["parallel"].insert("onentry");
	validChildren["parallel"].insert("onexit");
	validChildren["parallel"].insert("transition");
	validChildren["parallel"].insert("state");
	validChildren["parallel"].insert("parallel");
	validChildren["parallel"].insert("history");
	validChildren["parallel"].insert("datamodel");
	validChildren["parallel"].insert("invoke");

	validChildren["transition"] = execContentSet;
	validChildren["onentry"] = execContentSet;
	validChildren["onexit"] = execContentSet;
	validChildren["finalize"] = execContentSet;

	validChildren["if"] = execContentSet;
	validChildren["elseif"] = execContentSet;
	validChildren["else"] = execContentSet;
	validChildren["foreach"] = execContentSet;

	validChildren["initial"].insert("transition");
	validChildren["history"].insert("transition");

	validChildren["final"].insert("onentry");
	validChildren["final"].insert("onexit");
	validChildren["final"].insert("donedata");

	validChildren["datamodel"].insert("data");

	validChildren["donedata"].insert("content");
	validChildren["donedata"].insert("param");

	validChildren["send"].insert("content");
	validChildren["send"].insert("param");

	validChildren["invoke"].insert("content");
	validChildren["invoke"].insert("param");
	validChildren["invoke"].insert("finalize");

	// inverse validChildren to validParents
	std::map<std::string, std::set<std::string> > validParents;
	for (std::map<std::string, std::set<std::string> >::iterator parentIter = validChildren.begin(); parentIter != validChildren.end(); parentIter++) {
		for (std::set<std::string>::iterator childIter = parentIter->second.begin(); childIter != parentIter->second.end(); childIter++) {
			validParents[*childIter].insert(parentIter->first);
		}
	}


	for (auto stateIter = allStates.begin(); stateIter != allStates.end(); stateIter++) {
		DOMElement* state = static_cast<DOMElement*>(*stateIter);

		if (DOMUtils::isMember(state, finals) && !HAS_ATTR(state, kXMLCharId)) // id is not required for finals
			continue;

		// check for existance of id attribute - this not actually required!
		if (!HAS_ATTR(state, kXMLCharId)) {
			issues.push_back(InterpreterIssue("State has no 'id' attribute", state, InterpreterIssue::USCXML_ISSUE_FATAL));
			continue;
		}

		if (ATTR(state, kXMLCharId).size() == 0) {
			issues.push_back(InterpreterIssue("State has empty 'id' attribute", state, InterpreterIssue::USCXML_ISSUE_FATAL));
			continue;
		}

		std::string stateId = ATTR(state, kXMLCharId);

		// check for valid transition with history states
		if (LOCALNAME(state) == "history") {
			std::list<DOMElement*> transitions = DOMUtils::filterChildElements(XML_PREFIX(state).str() + "transition", state, false);
			if (transitions.size() > 1) {
				issues.push_back(InterpreterIssue("History pseudo-state with id '" + stateId + "' has multiple transitions", state, InterpreterIssue::USCXML_ISSUE_FATAL));
			} else if (transitions.size() == 0) {
				issues.push_back(InterpreterIssue("History pseudo-state with id '" + stateId + "' has no default transition", state, InterpreterIssue::USCXML_ISSUE_FATAL));
			} else {
				DOMElement* transition = static_cast<DOMElement*>(transitions.front());
				if (HAS_ATTR(transition, kXMLCharCond)) {
					issues.push_back(InterpreterIssue("Transition in history pseudo-state '" + stateId + "' must not have a condition", transition, InterpreterIssue::USCXML_ISSUE_FATAL));
				}
				if (HAS_ATTR(transition, kXMLCharEvent)) {
					issues.push_back(InterpreterIssue("Transition in history pseudo-state '" + stateId + "' must not have an event attribute", transition, InterpreterIssue::USCXML_ISSUE_FATAL));
				}
				if (!HAS_ATTR(transition, kXMLCharTarget)) {
					issues.push_back(InterpreterIssue("Transition in history pseudo-state '" + stateId + "' has no target", transition, InterpreterIssue::USCXML_ISSUE_FATAL));
				} else {
					std::list<DOMElement*> targetStates = getTargetStates(transition, _scxml);
					for (auto tIter = targetStates.begin(); tIter != targetStates.end(); tIter++) {
						DOMElement* target = *tIter;
						if (HAS_ATTR(state, kXMLCharType) && ATTR(state, kXMLCharType) == "deep") {
							if (!DOMUtils::isDescendant(target, state->getParentNode())) {
								issues.push_back(InterpreterIssue("Transition in deep history pseudo-state '" + stateId + "' has illegal target state '" + ATTR(target, kXMLCharId) + "'", transition, InterpreterIssue::USCXML_ISSUE_FATAL));
							}
						} else {
							if (target->getParentNode() != state->getParentNode()) {
								issues.push_back(InterpreterIssue("Transition in shallow history pseudo-state '" + stateId + "' has illegal target state '" + ATTR(target, kXMLCharId) + "'", transition, InterpreterIssue::USCXML_ISSUE_FATAL));
							}
						}
					}
				}
			}
		}

		// check whether state is reachable
		if (!DOMUtils::isMember(state, reachable) && areFromSameMachine(state, interpreter->_scxml)) {
			issues.push_back(InterpreterIssue("State with id '" + stateId + "' is unreachable", state, InterpreterIssue::USCXML_ISSUE_WARNING));
		}

		// check for uniqueness of id attribute
		if (seenStates.find(stateId) != seenStates.end()) {
			issues.push_back(InterpreterIssue("Duplicate state with id '" + stateId + "'", state, InterpreterIssue::USCXML_ISSUE_FATAL));
			continue;
		}
		seenStates[ATTR(state, kXMLCharId)] = state;
	}

	for (auto tIter = transitions.begin(); tIter != transitions.end(); tIter++) {
		DOMElement* transition = *tIter;

		// check for valid target
		if (HAS_ATTR(transition, kXMLCharTarget)) {
			std::list<std::string> targetIds = tokenize(ATTR(transition, kXMLCharTarget));
			if (targetIds.size() == 0) {
				issues.push_back(InterpreterIssue("Transition has empty target state list", transition, InterpreterIssue::USCXML_ISSUE_FATAL));
			}

			for (std::list<std::string>::iterator targetIter = targetIds.begin(); targetIter != targetIds.end(); targetIter++) {
				if (seenStates.find(*targetIter) == seenStates.end()) {
					issues.push_back(InterpreterIssue("Transition has non-existant target state with id '" + *targetIter + "'", transition, InterpreterIssue::USCXML_ISSUE_FATAL));
					continue;
				}
			}
		}
	}

	// check for redundancy of transition
	for (auto stateIter = allStates.begin(); stateIter != allStates.end(); stateIter++) {
		DOMElement* state = *stateIter;
		std::list<DOMElement*> transitions = DOMUtils::filterChildElements(XML_PREFIX(state).str() + "transition", state, false);

		for (auto tIter = transitions.begin(); tIter != transitions.end(); tIter++) {
			DOMElement* transition = *tIter;
			for (auto t2Iter = transitions.begin(); t2Iter != tIter; t2Iter++) {
				DOMElement* earlierTransition = *t2Iter;

				// will the earlier transition always be enabled when the later is?
				if (!HAS_ATTR(earlierTransition, kXMLCharCond)) {
					// earlier transition has no condition -> check event descriptor
					if (!HAS_ATTR(earlierTransition, kXMLCharEvent)) {
						// earlier transition is eventless
						issues.push_back(InterpreterIssue("Transition can never be optimally enabled", transition, InterpreterIssue::USCXML_ISSUE_INFO));
						goto NEXT_TRANSITION;

					} else if (HAS_ATTR(transition, kXMLCharEvent)) {
						// does the earlier transition match all our events?
						std::list<std::string> events = tokenize(ATTR(transition, kXMLCharEvent));

						bool allMatched = true;
						for (std::list<std::string>::iterator eventIter = events.begin(); eventIter != events.end(); eventIter++) {
							if (!nameMatch(ATTR(earlierTransition, kXMLCharEvent), *eventIter)) {
								allMatched = false;
								break;
							}
						}

						if (allMatched) {
							issues.push_back(InterpreterIssue("Transition can never be optimally enabled", transition, InterpreterIssue::USCXML_ISSUE_INFO));
							goto NEXT_TRANSITION;
						}
					}
				}
			}
NEXT_TRANSITION:
			;
		}
	}

	// check for useless history elements
	{
		for (auto histIter = histories.begin(); histIter != histories.end(); histIter++) {
			DOMElement* history = *histIter;

			if (!history->getParentNode() || history->getParentNode()->getNodeType() != DOMNode::ELEMENT_NODE)
				continue; // syntax check will have catched this

			DOMElement* parent = static_cast<DOMElement*>(history->getParentNode());
			if (isAtomic(parent)) {
				issues.push_back(InterpreterIssue("Useless history '" + ATTR(history, kXMLCharId) + "' in atomic state", history, InterpreterIssue::USCXML_ISSUE_INFO));
				continue;
			}
			std::list<std::set<const DOMElement* > > configs = getAllConfigurations(parent);
			if (configs.size() <= 1) {
				issues.push_back(InterpreterIssue("Useless history '" + ATTR(history, kXMLCharId) + "' in state with single legal configuration", history, InterpreterIssue::USCXML_ISSUE_INFO));
				continue;
			}
		}
	}

	// check for valid initial attribute
	{
		std::list<DOMElement*> withInitialAttr;
		withInitialAttr.insert(withInitialAttr.end(), allStates.begin(), allStates.end());
		withInitialAttr.push_back(_scxml);

		for (auto stateIter = withInitialAttr.begin(); stateIter != withInitialAttr.end(); stateIter++) {
			DOMElement* state = *stateIter;

			if (HAS_ATTR(state, kXMLCharInitial)) {
				std::list<DOMElement*> childs;
				std::list<DOMElement*> tmp;
				tmp = DOMUtils::filterChildElements(XML_PREFIX(state).str() + "state", state, true);
				childs.insert(childs.end(), tmp.begin(), tmp.end());
				tmp = DOMUtils::filterChildElements(XML_PREFIX(state).str() + "parallel", state, true);
				childs.insert(childs.end(), tmp.begin(), tmp.end());
				tmp = DOMUtils::filterChildElements(XML_PREFIX(state).str() + "final", state, true);
				childs.insert(childs.end(), tmp.begin(), tmp.end());
				tmp = DOMUtils::filterChildElements(XML_PREFIX(state).str() + "history", state, true);
				childs.insert(childs.end(), tmp.begin(), tmp.end());

				std::list<std::string> intials = tokenize(ATTR(state, kXMLCharInitial));
				for (std::list<std::string>::iterator initIter = intials.begin(); initIter != intials.end(); initIter++) {
					if (seenStates.find(*initIter) == seenStates.end()) {
						issues.push_back(InterpreterIssue("Initial attribute has invalid target state with id '" + *initIter + "'", state, InterpreterIssue::USCXML_ISSUE_FATAL));
						continue;
					}
					// value of the 'initial' attribute [..] must be descendants of the containing <state> or <parallel> element
					if (!DOMUtils::isMember(seenStates[*initIter], childs)) {
						issues.push_back(InterpreterIssue("Initial attribute references non-child state '" + *initIter + "'", state, InterpreterIssue::USCXML_ISSUE_FATAL));
					}
				}
			}
		}
	}

	// check for legal configuration of target sets
	{
		std::map<DOMElement*, std::string > targetIdSets;
		for (auto iter = transitions.begin(); iter != transitions.end(); iter++) {
			DOMElement* transition = *iter;

			if (HAS_ATTR(transition, kXMLCharTarget)) {
				targetIdSets[transition] = ATTR(transition, kXMLCharTarget);
			}
		}

		for (auto iter = initials.begin(); iter != initials.end(); iter++) {
			DOMElement* initial = *iter;

			if (HAS_ATTR(initial, kXMLCharTarget)) {
				targetIdSets[initial] = ATTR(initial, kXMLCharTarget);
			}
		}

		for (auto iter = allStates.begin(); iter != allStates.end(); iter++) {
			DOMElement* state = *iter;

			if (HAS_ATTR(state, kXMLCharInitial)) {
				targetIdSets[state] = ATTR(state, kXMLCharInitial);
			}
		}

		for (auto setIter = targetIdSets.begin();
		        setIter != targetIdSets.end();
		        setIter++) {
			std::list<DOMElement*> targets;
			std::list<std::string> targetIds = tokenize(setIter->second);
			for (auto tgtIter = targetIds.begin(); tgtIter != targetIds.end(); tgtIter++) {
				if (seenStates.find(*tgtIter) == seenStates.end())
					goto NEXT_SET;
				targets.push_back(seenStates[*tgtIter]);
			}
			if (!hasLegalCompletion(targets)) {
				issues.push_back(InterpreterIssue("Target states cause illegal configuration", setIter->first, InterpreterIssue::USCXML_ISSUE_FATAL));
			}
NEXT_SET:
			;
		}
	}

	// check for valid initial transition
	{
		std::list<DOMElement*> initTrans;

		for (auto iter = initials.begin(); iter != initials.end(); iter++) {
			DOMElement* initial = *iter;

			std::list<DOMElement*> initTransitions = DOMUtils::filterChildElements(XML_PREFIX(initial).str() + "transition", initial, true);
			if (initTransitions.size() != 1) {
				issues.push_back(InterpreterIssue("Initial element must define exactly one transition", initial, InterpreterIssue::USCXML_ISSUE_FATAL));
			}
			initTrans.insert(initTrans.end(), initTransitions.begin(), initTransitions.end());

		}

		for (auto iter = initTrans.begin(); iter != initTrans.end(); iter++) {
			DOMElement* transition = *iter;

			/* In a conformant SCXML document, this transition must not contain 'cond' or 'event' attributes, and must specify a non-null 'target'
			 * whose value is a valid state specification consisting solely of descendants of the containing state
			 */

			if (HAS_ATTR(transition, kXMLCharCond)) {
				issues.push_back(InterpreterIssue("Initial transition cannot have a condition", transition, InterpreterIssue::USCXML_ISSUE_FATAL));
			}
			if (HAS_ATTR(transition, kXMLCharEvent)) {
				issues.push_back(InterpreterIssue("Initial transition cannot be eventful", transition, InterpreterIssue::USCXML_ISSUE_FATAL));
			}

			if (!transition->getParentNode() ||
			        !transition->getParentNode()->getParentNode() ||
			        transition->getParentNode()->getParentNode()->getNodeType() != DOMNode::ELEMENT_NODE)
				continue; // syntax will catch this one
			DOMElement* state = static_cast<DOMElement*>(transition->getParentNode()->getParentNode());
			if (!isState(state))
				continue; // syntax will catch this one

			std::list<DOMElement*> childs;
			std::list<DOMElement*> tmp;
			tmp = DOMUtils::filterChildElements(XML_PREFIX(state).str() + "state", state, true);
			childs.insert(childs.end(), tmp.begin(), tmp.end());
			tmp = DOMUtils::filterChildElements(XML_PREFIX(state).str() + "parallel", state, true);
			childs.insert(childs.end(), tmp.begin(), tmp.end());
			tmp = DOMUtils::filterChildElements(XML_PREFIX(state).str() + "final", state, true);
			childs.insert(childs.end(), tmp.begin(), tmp.end());
			tmp = DOMUtils::filterChildElements(XML_PREFIX(state).str() + "history", state, true);
			childs.insert(childs.end(), tmp.begin(), tmp.end());

			std::list<std::string> intials = tokenize(ATTR(transition, kXMLCharTarget));
			for (std::list<std::string>::iterator initIter = intials.begin(); initIter != intials.end(); initIter++) {
				// the 'target' of a <transition> inside an <initial> or <history> element: all the states must be descendants of the containing <state> or <parallel> element
				if (!DOMUtils::isMember(seenStates[*initIter], childs)) {
					issues.push_back(InterpreterIssue("Target of initial transition references non-child state '" + *initIter + "'", transition, InterpreterIssue::USCXML_ISSUE_FATAL));
				}
			}
		}
	}


	// check that all invokers exists
	{
		for (auto iter = invokes.begin(); iter != invokes.end(); iter++) {
			DOMElement* invoke = *iter;
			if (HAS_ATTR(invoke, kXMLCharType) && !_factory->hasInvoker(ATTR(invoke, kXMLCharType))) {
				// unknown at factory - adhoc extension?
				if (HAS_ATTR(invoke, kXMLCharId) && interpreter->_invokers.find(ATTR(invoke, kXMLCharId)) != interpreter->_invokers.end())
					continue; // not an issue

				IssueSeverity severity;
				if (HAS_ATTR(invoke, kXMLCharIdLocation)) {
					// we might still resolve at runtime
					severity = InterpreterIssue::USCXML_ISSUE_WARNING;
				} else {
					// fatality!
					severity = InterpreterIssue::USCXML_ISSUE_FATAL;
				}
				issues.push_back(InterpreterIssue("Invoke with unknown type '" + ATTR(invoke, kXMLCharType) + "'", invoke, severity));
				continue;
			}
		}
	}

	// check that all io processors exists
	{
		for (auto iter = sends.begin(); iter != sends.end(); iter++) {
			DOMElement* send = *iter;
			if (HAS_ATTR(send, kXMLCharType) && !_factory->hasIOProcessor(ATTR(send, kXMLCharType))) {
				if (interpreter->_ioProcs.find(ATTR(send, kXMLCharType)) != interpreter->_ioProcs.end())
					continue; // not an issue, available ad-hoc

				issues.push_back(InterpreterIssue("Send to unknown IO Processor '" + ATTR(send, kXMLCharType) + "'", send, InterpreterIssue::USCXML_ISSUE_FATAL));
				continue;
			}
		}
	}

	// check that all custom executable content is known
	{
		std::list<DOMElement*> allExecContentContainers;
		allExecContentContainers.insert(allExecContentContainers.end(), onEntries.begin(), onEntries.end());
		allExecContentContainers.insert(allExecContentContainers.end(), onExits.begin(), onExits.end());
		allExecContentContainers.insert(allExecContentContainers.end(), transitions.begin(), transitions.end());
		allExecContentContainers.insert(allExecContentContainers.end(), finalizes.begin(), finalizes.end());

		for (auto bIter = allExecContentContainers.begin(); bIter != allExecContentContainers.end(); bIter++) {
			DOMElement* block = *bIter;
			std::list<DOMNode*> execContents = DOMUtils::filterChildType(DOMNode::ELEMENT_NODE, block);
			for (auto ecIter = execContents.begin(); ecIter != execContents.end(); ecIter++) {
				DOMElement* execContent = static_cast<DOMElement*>(*ecIter);
				// SCXML specific executable content, always available
				if (DOMUtils::isMember(execContent, allExecContents)) {
					continue;
				}

				if (!_factory->hasExecutableContent(X(execContent->getLocalName()), X(execContent->getNamespaceURI()))) {
					issues.push_back(InterpreterIssue("Executable content element '" + (std::string)X(execContent->getLocalName()) + "' in namespace '" + (std::string)X(execContent->getNamespaceURI()) + "' unknown", execContent, InterpreterIssue::USCXML_ISSUE_FATAL));
					continue;
				}
			}
		}
	}

	// check that all SCXML elements have valid parents and required attributes
	{
		for (auto iter = allElements.begin(); iter != allElements.end(); iter++) {
			DOMElement* element = *iter;
			std::string localName = LOCALNAME(element);

			if (reqAttr.find(localName) != reqAttr.end()) {
				for (std::set<std::string>::const_iterator reqIter = reqAttr[localName].begin();
				        reqIter != reqAttr[localName].end(); reqIter++) {
					if (!HAS_ATTR(element, X(*reqIter))) {
						issues.push_back(InterpreterIssue("Element " + localName + " is missing required attribute '" + *reqIter + "'", element, InterpreterIssue::USCXML_ISSUE_WARNING));
					}
					if (HAS_ATTR(element, X(*reqIter)) && ATTR(element, X(*reqIter)).size() == 0) {
						issues.push_back(InterpreterIssue("Required attribute '" + *reqIter + "' of element " + localName + " is empty", element, InterpreterIssue::USCXML_ISSUE_WARNING));
					}
				}
			}

			if (localName == "scxml") // can be anywhere: <assign>, <content>, <other:embed>
				continue;

			if (!element->getParentNode() || element->getParentNode()->getNodeType() != DOMNode::ELEMENT_NODE) {
				issues.push_back(InterpreterIssue("Parent of " + localName + " is no element", element, InterpreterIssue::USCXML_ISSUE_WARNING));
				continue;
			}

			DOMElement* parent = static_cast<DOMElement*>(element->getParentNode());
			std::string parentName = LOCALNAME(parent);

			if (validParents[localName].find(parentName) == validParents[localName].end()) {
				issues.push_back(InterpreterIssue("Element " + localName + " can be no child of " + parentName, element, InterpreterIssue::USCXML_ISSUE_WARNING));
				continue;
			}
		}
	}

	// check attribute constraints
	{
		for (auto iter = initials.begin(); iter != initials.end(); iter++) {
			DOMElement* initial = *iter;
			if (initial->getParentNode() && initial->getParentNode()->getNodeType() == DOMNode::ELEMENT_NODE) {
				DOMElement* state = static_cast<DOMElement*>(initial->getParentNode());
				if (HAS_ATTR(state, kXMLCharInitial)) {
					issues.push_back(InterpreterIssue("State with initial attribute cannot have <initial> child ", state, InterpreterIssue::USCXML_ISSUE_WARNING));
				}
				if (isAtomic(state)) {
					issues.push_back(InterpreterIssue("Atomic state cannot have <initial> child ", state, InterpreterIssue::USCXML_ISSUE_WARNING));
				}
			}
		}
		for (auto iter = allStates.begin(); iter != allStates.end(); iter++) {
			DOMElement* state = *iter;
			if (isAtomic(state) && HAS_ATTR(state, kXMLCharInitial)) {
				issues.push_back(InterpreterIssue("Atomic state cannot have initial attribute ", state, InterpreterIssue::USCXML_ISSUE_WARNING));
			}
		}

		for (auto iter = assigns.begin(); iter != assigns.end(); iter++) {
			DOMElement* assign = *iter;
			if (HAS_ATTR(assign, kXMLCharExpr) && assign->getChildNodes()->getLength() > 0) {
				issues.push_back(InterpreterIssue("Assign element cannot have expr attribute and children", assign, InterpreterIssue::USCXML_ISSUE_WARNING));
			}
		}

		for (auto iter = contents.begin(); iter != contents.end(); iter++) {
			DOMElement* content = *iter;
			if (HAS_ATTR(content, kXMLCharExpr) && content->getChildNodes()->getLength() > 0) {
				issues.push_back(InterpreterIssue("Content element cannot have expr attribute and children", content, InterpreterIssue::USCXML_ISSUE_WARNING));
			}
		}

		for (auto iter = params.begin(); iter != params.end(); iter++) {
			DOMElement* param = *iter;
			if (HAS_ATTR(param, kXMLCharExpr) && HAS_ATTR(param, kXMLCharLocation)) {
				issues.push_back(InterpreterIssue("Param element cannot have both expr and location attribute", param, InterpreterIssue::USCXML_ISSUE_WARNING));
			}
		}

		for (auto iter = scripts.begin(); iter != scripts.end(); iter++) {
			DOMElement* script = *iter;
			if (HAS_ATTR(script, kXMLCharSource) && script->getChildNodes()->getLength() > 0) {
				issues.push_back(InterpreterIssue("Script element cannot have src attribute and children", script, InterpreterIssue::USCXML_ISSUE_WARNING));
			}
		}

		for (auto iter = sends.begin(); iter != sends.end(); iter++) {
			DOMElement* send = *iter;
			if (HAS_ATTR(send, kXMLCharEvent) && HAS_ATTR(send, kXMLCharEventExpr)) {
				issues.push_back(InterpreterIssue("Send element cannot have both event and eventexpr attribute", send, InterpreterIssue::USCXML_ISSUE_WARNING));
			}
			if (HAS_ATTR(send, kXMLCharTarget) && HAS_ATTR(send, kXMLCharTargetExpr)) {
				issues.push_back(InterpreterIssue("Send element cannot have both target and targetexpr attribute", send, InterpreterIssue::USCXML_ISSUE_WARNING));
			}
			if (HAS_ATTR(send, kXMLCharType) && HAS_ATTR(send, kXMLCharTypeExpr)) {
				issues.push_back(InterpreterIssue("Send element cannot have both type and typeexpr attribute", send, InterpreterIssue::USCXML_ISSUE_WARNING));
			}
			if (HAS_ATTR(send, kXMLCharId) && HAS_ATTR(send, kXMLCharIdLocation)) {
				issues.push_back(InterpreterIssue("Send element cannot have both id and idlocation attribute", send, InterpreterIssue::USCXML_ISSUE_WARNING));
			}
			if (HAS_ATTR(send, kXMLCharDelay) && HAS_ATTR(send, kXMLCharDelayExpr)) {
				issues.push_back(InterpreterIssue("Send element cannot have both delay and delayexpr attribute", send, InterpreterIssue::USCXML_ISSUE_WARNING));
			}
			if (HAS_ATTR(send, kXMLCharDelay) && HAS_ATTR(send, kXMLCharTarget) && ATTR(send, kXMLCharTarget)== "_internal") {
				issues.push_back(InterpreterIssue("Send element cannot have delay with target _internal", send, InterpreterIssue::USCXML_ISSUE_WARNING));
			}

			std::list<DOMElement*> contentChilds = DOMUtils::filterChildElements(XML_PREFIX(send).str() + "content", send, false);
			std::list<DOMElement*> paramChilds = DOMUtils::filterChildElements(XML_PREFIX(send).str() + "param", send, false);

			if (HAS_ATTR(send, kXMLCharNameList) && contentChilds.size() > 0) {
				issues.push_back(InterpreterIssue("Send element cannot have namelist attribute and content child", send, InterpreterIssue::USCXML_ISSUE_WARNING));
			}

			if (paramChilds.size() > 0 && contentChilds.size() > 0) {
				issues.push_back(InterpreterIssue("Send element cannot have param child and content child", send, InterpreterIssue::USCXML_ISSUE_WARNING));
			}

		}
		for (auto iter = cancels.begin(); iter != cancels.end(); iter++) {
			DOMElement* cancel = *iter;
			if (HAS_ATTR(cancel, kXMLCharSendId) && HAS_ATTR(cancel, kXMLCharSendIdExpr)) {
				issues.push_back(InterpreterIssue("Cancel element cannot have both sendid and eventexpr sendidexpr", cancel, InterpreterIssue::USCXML_ISSUE_WARNING));
			}
		}

		for (auto iter = invokes.begin(); iter != invokes.end(); iter++) {
			DOMElement* invoke = *iter;
			if (HAS_ATTR(invoke, kXMLCharType) && HAS_ATTR(invoke, kXMLCharTypeExpr)) {
				issues.push_back(InterpreterIssue("Invoke element cannot have both type and typeexpr attribute", invoke, InterpreterIssue::USCXML_ISSUE_WARNING));
			}
			if (HAS_ATTR(invoke, kXMLCharSource) && HAS_ATTR(invoke, kXMLCharSourceExpr)) {
				issues.push_back(InterpreterIssue("Invoke element cannot have both src and srcexpr attribute", invoke, InterpreterIssue::USCXML_ISSUE_WARNING));
			}
			if (HAS_ATTR(invoke, kXMLCharId) && HAS_ATTR(invoke, kXMLCharIdLocation)) {
				issues.push_back(InterpreterIssue("Invoke element cannot have both id and idlocation attribute", invoke, InterpreterIssue::USCXML_ISSUE_WARNING));
			}
			if (HAS_ATTR(invoke, kXMLCharNameList) && DOMUtils::filterChildElements(XML_PREFIX(invoke).str() + "param", invoke, false).size() > 0) {
				issues.push_back(InterpreterIssue("Invoke element cannot have namelist attribute and param child", invoke, InterpreterIssue::USCXML_ISSUE_WARNING));
			}
			if (HAS_ATTR(invoke, kXMLCharSource) && DOMUtils::filterChildElements(XML_PREFIX(invoke).str() + "content", invoke, false).size() > 0) {
				issues.push_back(InterpreterIssue("Invoke element cannot have src attribute and content child", invoke, InterpreterIssue::USCXML_ISSUE_WARNING));

			}
		}
		for (auto iter = doneDatas.begin(); iter != doneDatas.end(); iter++) {
			DOMElement* donedata = *iter;
			if (DOMUtils::filterChildElements(XML_PREFIX(donedata).str() + "content", donedata, false).size() > 0 &&
			        DOMUtils::filterChildElements(XML_PREFIX(donedata).str() + "param", donedata, false).size() > 0) {
				issues.push_back(InterpreterIssue("Donedata element cannot have param child and content child", donedata, InterpreterIssue::USCXML_ISSUE_WARNING));

			}
		}
	}

	// check that the datamodel is known if not already instantiated
	if (!interpreter->_dataModel) {
		if (HAS_ATTR(_scxml, kXMLCharDataModel)) {
			if (!_factory->hasDataModel(ATTR(_scxml, kXMLCharDataModel))) {
				issues.push_back(InterpreterIssue("SCXML document requires unknown datamodel '" + ATTR(_scxml, kXMLCharDataModel) + "'", _scxml, InterpreterIssue::USCXML_ISSUE_FATAL));

				// we cannot even check the rest as we require a datamodel
				return issues;
			}
		}
	}

	bool instantiatedDataModel = false;
	// instantiate datamodel if not explicitly set
	if (!_dataModel) {
		if (HAS_ATTR(_scxml, kXMLCharDataModel)) {
			// might throw
			_dataModel = _factory->createDataModel(ATTR(_scxml, kXMLCharDataModel), interpreter);
			instantiatedDataModel = true;
		} else {
			_dataModel = _factory->createDataModel("null", interpreter);
		}
	}


	// test all scripts for valid syntax
	{
		for (auto iter = scripts.begin(); iter != scripts.end(); iter++) {
			DOMElement* script = *iter;

			if (script->hasChildNodes()) {
				// search for the text node with the actual script
				std::string scriptContent;
				for (DOMNode* child = script->getFirstChild(); child; child = child->getNextSibling()) {
					if (child->getNodeType() == DOMNode::TEXT_NODE || child->getNodeType() == DOMNode::CDATA_SECTION_NODE)
						scriptContent += (std::string)X(child->getNodeValue());
				}

				if (!_dataModel.isValidSyntax(scriptContent)) {
					issues.push_back(InterpreterIssue("Syntax error in script", script, InterpreterIssue::USCXML_ISSUE_WARNING));
				}
			}
		}
	}

	// test the various attributes with datamodel expressions for valid syntax
	{
		std::list<DOMElement*> withCondAttrs;
		withCondAttrs.insert(withCondAttrs.end(), transitions.begin(), transitions.end());
		withCondAttrs.insert(withCondAttrs.end(), ifs.begin(), ifs.end());
		withCondAttrs.insert(withCondAttrs.end(), elseIfs.begin(), elseIfs.end());

		for (auto iter = withCondAttrs.begin(); iter != withCondAttrs.end(); iter++) {
			DOMElement* condAttr = *iter;
			if (HAS_ATTR(condAttr, kXMLCharCond)) {
				if (!_dataModel.isValidSyntax(ATTR(condAttr, kXMLCharCond))) {
					issues.push_back(InterpreterIssue("Syntax error in cond attribute", condAttr, InterpreterIssue::USCXML_ISSUE_WARNING));
					continue;
				}
			}
		}
	}

	{
		std::list<DOMElement*> withExprAttrs;
		withExprAttrs.insert(withExprAttrs.end(), logs.begin(), logs.end());
		withExprAttrs.insert(withExprAttrs.end(), datas.begin(), datas.end());
		withExprAttrs.insert(withExprAttrs.end(), assigns.begin(), assigns.end());
		withExprAttrs.insert(withExprAttrs.end(), contents.begin(), contents.end());
		withExprAttrs.insert(withExprAttrs.end(), params.begin(), params.end());

		for (auto iter = withExprAttrs.begin(); iter != withExprAttrs.end(); iter++) {
			DOMElement* withExprAttr = *iter;
			if (HAS_ATTR(withExprAttr, kXMLCharExpr)) {
				if (DOMUtils::isMember(withExprAttr, datas) || DOMUtils::isMember(withExprAttr, assigns)) {
					if (!_dataModel.isValidSyntax("foo = " + ATTR(withExprAttr, kXMLCharExpr))) { // TODO: this is ECMAScripty!
						issues.push_back(InterpreterIssue("Syntax error in expr attribute", withExprAttr, InterpreterIssue::USCXML_ISSUE_WARNING));
						continue;
					}
				} else {
					if (!_dataModel.isValidSyntax(ATTR(withExprAttr, kXMLCharExpr))) {
						issues.push_back(InterpreterIssue("Syntax error in expr attribute", withExprAttr, InterpreterIssue::USCXML_ISSUE_WARNING));
						continue;
					}
				}
			}
		}
	}

	{
		for (auto iter = foreachs.begin(); iter != foreachs.end(); iter++) {
			DOMElement* foreach = *iter;
			if (HAS_ATTR(foreach, kXMLCharArray)) {
				if (!_dataModel.isValidSyntax(ATTR(foreach, kXMLCharArray))) {
					issues.push_back(InterpreterIssue("Syntax error in array attribute", foreach, InterpreterIssue::USCXML_ISSUE_WARNING));
				}
			}
			if (HAS_ATTR(foreach, kXMLCharItem)) {
				if (!_dataModel.isValidSyntax(ATTR(foreach, kXMLCharItem))) {
					issues.push_back(InterpreterIssue("Syntax error in item attribute", foreach, InterpreterIssue::USCXML_ISSUE_WARNING));
				}
			}
			if (HAS_ATTR(foreach, kXMLCharIndex)) {
				if (!_dataModel.isValidSyntax(ATTR(foreach, kXMLCharIndex))) {
					issues.push_back(InterpreterIssue("Syntax error in index attribute", foreach, InterpreterIssue::USCXML_ISSUE_WARNING));
				}
			}
		}
	}

	{
		for (auto iter = sends.begin(); iter != sends.end(); iter++) {
			DOMElement* send = *iter;
			if (HAS_ATTR(send, kXMLCharEventExpr)) {
				if (!_dataModel.isValidSyntax(ATTR(send, kXMLCharEventExpr))) {
					issues.push_back(InterpreterIssue("Syntax error in eventexpr attribute", send, InterpreterIssue::USCXML_ISSUE_WARNING));
				}
			}
			if (HAS_ATTR(send, kXMLCharTargetExpr)) {
				if (!_dataModel.isValidSyntax(ATTR(send, kXMLCharTargetExpr))) {
					issues.push_back(InterpreterIssue("Syntax error in targetexpr attribute", send, InterpreterIssue::USCXML_ISSUE_WARNING));
				}
			}
			if (HAS_ATTR(send, kXMLCharTypeExpr)) {
				if (!_dataModel.isValidSyntax(ATTR(send, kXMLCharTypeExpr))) {
					issues.push_back(InterpreterIssue("Syntax error in typeexpr attribute", send, InterpreterIssue::USCXML_ISSUE_WARNING));
				}
			}
			if (HAS_ATTR(send, kXMLCharIdLocation)) {
				if (!_dataModel.isValidSyntax(ATTR(send, kXMLCharIdLocation))) {
					issues.push_back(InterpreterIssue("Syntax error in idlocation attribute", send, InterpreterIssue::USCXML_ISSUE_WARNING));
				}
			}
			if (HAS_ATTR(send, kXMLCharDelayExpr)) {
				if (!_dataModel.isValidSyntax(ATTR(send, kXMLCharDelayExpr))) {
					issues.push_back(InterpreterIssue("Syntax error in delayexpr attribute", send, InterpreterIssue::USCXML_ISSUE_WARNING));
				}
			}
		}

	}

	{
		for (auto iter = invokes.begin(); iter != invokes.end(); iter++) {
			DOMElement* invoke = *iter;
			if (HAS_ATTR(invoke, kXMLCharTypeExpr)) {
				if (!_dataModel.isValidSyntax(ATTR(invoke, kXMLCharTypeExpr))) {
					issues.push_back(InterpreterIssue("Syntax error in typeexpr attribute", invoke, InterpreterIssue::USCXML_ISSUE_WARNING));
					continue;
				}
			}
			if (HAS_ATTR(invoke, kXMLCharSourceExpr)) {
				if (!_dataModel.isValidSyntax(ATTR(invoke, kXMLCharSourceExpr))) {
					issues.push_back(InterpreterIssue("Syntax error in srcexpr attribute", invoke, InterpreterIssue::USCXML_ISSUE_WARNING));
					continue;
				}
			}
			if (HAS_ATTR(invoke, kXMLCharIdLocation)) {
				if (!_dataModel.isValidSyntax(ATTR(invoke, kXMLCharIdLocation))) {
					issues.push_back(InterpreterIssue("Syntax error in idlocation attribute", invoke, InterpreterIssue::USCXML_ISSUE_WARNING));
					continue;
				}
			}
		}
	}

	{
		for (auto iter = cancels.begin(); iter != cancels.end(); iter++) {
			DOMElement* cancel = *iter;
			if (HAS_ATTR(cancel, kXMLCharSendIdExpr)) {
				if (!_dataModel.isValidSyntax(ATTR(cancel, kXMLCharSendIdExpr))) {
					issues.push_back(InterpreterIssue("Syntax error in sendidexpr attribute", cancel, InterpreterIssue::USCXML_ISSUE_WARNING));
					continue;
				}
			}
		}
	}

	if (instantiatedDataModel)
		_dataModel = DataModel();

	return issues;
}

std::ostream& operator<< (std::ostream& os, const InterpreterIssue& issue) {
	switch (issue.severity) {
	case InterpreterIssue::USCXML_ISSUE_FATAL:
		os << "Issue (FATAL) ";
		break;
	case InterpreterIssue::USCXML_ISSUE_WARNING:
		os << "Issue (WARNING) ";
		break;
	case InterpreterIssue::USCXML_ISSUE_INFO:
		os << "Issue (INFO) ";
		break;
	default:
		break;
	}

	if (issue.xPath.size() > 0) {
		os << "at " << issue.xPath << ": ";
	} else {
		os << ": ";
	}
	os << issue.message;
	return os;
}


}
