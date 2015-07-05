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
#include "uscxml/DOMUtils.h"
#include "uscxml/debug/Complexity.h"
#include "uscxml/Interpreter.h"
#include "uscxml/Factory.h"

#include <XPath/XPath.hpp>
#include <DOM/Document.hpp>

namespace uscxml {

using namespace Arabica::XPath;
using namespace Arabica::DOM;

InterpreterIssue::InterpreterIssue(const std::string& msg, Arabica::DOM::Node<std::string> node, IssueSeverity severity) : message(msg), node(node), severity(severity) {
	if (node)
		xPath = DOMUtils::xPathForNode(node);
}

// find all elements in the SCXML namespace in one traversal
void assembleNodeSets(const std::string nsPrefix, const Node<std::string>& node, std::map<std::string, NodeSet<std::string> >& sets) {
	NodeList<std::string> childs = node.getChildNodes();
	for (unsigned int i = 0; i < childs.getLength(); i++) {
		if (childs.item(i).getNodeType() != Node_base::ELEMENT_NODE)
			continue;
		//		std::cout << TAGNAME(childs.item(i)) << std::endl;

		if (TAGNAME_CAST(childs.item(i)).find(nsPrefix) == 0) {
			// correct namespace, insert via localname
			sets[LOCALNAME_CAST(childs.item(i))].push_back(childs.item(i));
		}
		assembleNodeSets(nsPrefix, childs.item(i), sets);
	}
}


/**
 * Can the given states ever appear in an active configuration?
 */
bool hasLegalCompletion(const NodeSet<std::string>& states) {
    if (states.size() < 2)
        return true;
    
    // iterate every pair
    for (unsigned int outer = 0; outer < states.size() - 1; outer++) {
        Element<std::string> s1(states[outer]);
        for (unsigned int inner = outer + 1; inner < states.size(); inner++) {
            Element<std::string> s2(states[inner]);
            Node<std::string> parent;
            
            // ok to be directly ancestorally related
            if (InterpreterImpl::isDescendant(s1, s2) || InterpreterImpl::isDescendant(s2, s1))
                goto NEXT_PAIR;
            
            // find least common ancestor
            parent = s1.getParentNode();
            while(parent && parent.getNodeType() == Node_base::ELEMENT_NODE) {
                if (InterpreterImpl::isDescendant(s2, parent)) {
                    if (InterpreterImpl::isParallel(Element<std::string>(parent)))
                        goto NEXT_PAIR;
                }
                parent = parent.getParentNode();
            }
            
            return false;
        NEXT_PAIR:;
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
		InterpreterIssue issue("No SCXML element to be found", Node<std::string>(), InterpreterIssue::USCXML_ISSUE_FATAL);
		issues.push_back(issue);
		return issues;
	}

	std::map<std::string, Arabica::DOM::Element<std::string> > seenStates;

	// get some aliases
	Element<std::string>& _scxml = interpreter->_scxml;
	NameSpaceInfo& _nsInfo = interpreter->_nsInfo;
	Factory* _factory = interpreter->_factory;
	DataModel& _dataModel = interpreter->_dataModel;


	std::map<std::string, NodeSet<std::string> > nodeSets;
	assembleNodeSets(_nsInfo.xmlNSPrefix, _scxml, nodeSets);


	NodeSet<std::string> scxmls = nodeSets["scxml"];
	scxmls.push_back(_scxml);

	NodeSet<std::string> reachable = interpreter->getReachableStates();

	NodeSet<std::string>& states = nodeSets["state"];
	NodeSet<std::string>& parallels = nodeSets["parallel"];
	NodeSet<std::string>& transitions = nodeSets["transition"];
	NodeSet<std::string>& initials = nodeSets["initial"];
	NodeSet<std::string>& finals = nodeSets["final"];
	NodeSet<std::string>& onEntries = nodeSets["onentry"];
	NodeSet<std::string>& onExits = nodeSets["onexit"];
	NodeSet<std::string>& histories = nodeSets["history"];

	NodeSet<std::string>& raises = nodeSets["raise"];
	NodeSet<std::string>& ifs = nodeSets["if"];
	NodeSet<std::string>& elseIfs = nodeSets["elseif"];
	NodeSet<std::string>& elses = nodeSets["else"];
	NodeSet<std::string>& foreachs = nodeSets["foreach"];
	NodeSet<std::string>& logs = nodeSets["log"];

	NodeSet<std::string>& dataModels = nodeSets["datamodel"];
	NodeSet<std::string>& datas = nodeSets["data"];
	NodeSet<std::string>& assigns = nodeSets["assign"];
	NodeSet<std::string>& doneDatas = nodeSets["donedata"];
	NodeSet<std::string>& contents = nodeSets["content"];
	NodeSet<std::string>& params = nodeSets["param"];
	NodeSet<std::string>& scripts = nodeSets["script"];

	NodeSet<std::string>& sends = nodeSets["send"];
	NodeSet<std::string>& cancels = nodeSets["cancel"];
	NodeSet<std::string>& invokes = nodeSets["invoke"];
	NodeSet<std::string>& finalizes = nodeSets["finalize"];

	NodeSet<std::string> allStates;
	allStates.push_back(states);
	allStates.push_back(parallels);
	allStates.push_back(histories);
	allStates.push_back(finals);

	NodeSet<std::string> allExecContents;
	allExecContents.push_back(raises);
	allExecContents.push_back(ifs);
	allExecContents.push_back(elseIfs);
	allExecContents.push_back(elses);
	allExecContents.push_back(foreachs);
	allExecContents.push_back(logs);
	allExecContents.push_back(sends);
	allExecContents.push_back(assigns);
	allExecContents.push_back(scripts);
	allExecContents.push_back(cancels);

	NodeSet<std::string> allElements;
    allElements.push_back(scxmls);
    allElements.push_back(allStates);
	allElements.push_back(allExecContents);
	allElements.push_back(transitions);
	allElements.push_back(initials);
	allElements.push_back(onEntries);
	allElements.push_back(onExits);
	allElements.push_back(dataModels);
	allElements.push_back(datas);
	allElements.push_back(doneDatas);
	allElements.push_back(contents);
	allElements.push_back(params);
	allElements.push_back(invokes);
	allElements.push_back(finalizes);


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


	for (int i = 0; i < allStates.size(); i++) {
		Element<std::string> state = Element<std::string>(allStates[i]);

		if (InterpreterImpl::isMember(state, finals) && !HAS_ATTR(state, "id")) // id is not required for finals
			continue;

		// check for existance of id attribute - this not actually required!
		if (!HAS_ATTR(state, "id")) {
			issues.push_back(InterpreterIssue("State has no 'id' attribute", state, InterpreterIssue::USCXML_ISSUE_FATAL));
			continue;
		}

		if (ATTR(state, "id").size() == 0) {
			issues.push_back(InterpreterIssue("State has empty 'id' attribute", state, InterpreterIssue::USCXML_ISSUE_FATAL));
			continue;
		}

		std::string stateId = ATTR(state, "id");

		// check for valid transition with history states
		if (LOCALNAME(state) == "history") {
			NodeSet<std::string> transitions = InterpreterImpl::filterChildElements(_nsInfo.xmlNSPrefix + "transition", state, false);
			if (transitions.size() > 1) {
				issues.push_back(InterpreterIssue("History pseudo-state with id '" + stateId + "' has multiple transitions", state, InterpreterIssue::USCXML_ISSUE_FATAL));
			} else if (transitions.size() == 1) {
				Element<std::string> transition = Element<std::string>(transitions[0]);
				if (HAS_ATTR(transition, "cond")) {
					issues.push_back(InterpreterIssue("Transition in history pseudo-state '" + stateId + "' must not have a condition", transition, InterpreterIssue::USCXML_ISSUE_FATAL));
				}
				if (HAS_ATTR(transition, "event")) {
					issues.push_back(InterpreterIssue("Transition in history pseudo-state '" + stateId + "' must not have an event attribute", transition, InterpreterIssue::USCXML_ISSUE_FATAL));
				}
				if (!HAS_ATTR(transition, "target")) {
					issues.push_back(InterpreterIssue("Transition in history pseudo-state '" + stateId + "' has no target", transition, InterpreterIssue::USCXML_ISSUE_FATAL));
				} else {
					NodeSet<std::string> targetStates = interpreter->getTargetStates(transition);
					for (int j = 0; j < targetStates.size(); j++) {
						Element<std::string> target = Element<std::string>(targetStates[j]);
						if (HAS_ATTR(state, "type") && ATTR(state, "type") == "deep") {
							if (!InterpreterImpl::isDescendant(target, state.getParentNode())) {
								issues.push_back(InterpreterIssue("Transition in deep history pseudo-state '" + stateId + "' has invalid target state '" + ATTR(target, "id") + "'", transition, InterpreterIssue::USCXML_ISSUE_FATAL));
							}
						} else {
							if (target.getParentNode() != state.getParentNode()) {
								issues.push_back(InterpreterIssue("Transition in shallow history pseudo-state '" + stateId + "' has invalid target state '" + ATTR(target, "id") + "'", transition, InterpreterIssue::USCXML_ISSUE_FATAL));
							}
						}
					}
				}
			}
		}

		// check whether state is reachable
		if (!InterpreterImpl::isMember(state, reachable) && !InterpreterImpl::isInEmbeddedDocument(state)) {
			issues.push_back(InterpreterIssue("State with id '" + stateId + "' is unreachable", state, InterpreterIssue::USCXML_ISSUE_FATAL));
		}

		// check for uniqueness of id attribute
		if (seenStates.find(stateId) != seenStates.end()) {
			issues.push_back(InterpreterIssue("Duplicate state with id '" + stateId + "'", state, InterpreterIssue::USCXML_ISSUE_FATAL));
			continue;
		}
		seenStates[ATTR(state, "id")] = state;
	}

	for (int i = 0; i < transitions.size(); i++) {
		Element<std::string> transition = Element<std::string>(transitions[i]);

		// check for valid target
		if (HAS_ATTR(transition, "target")) {
			std::list<std::string> targetIds = InterpreterImpl::tokenizeIdRefs(ATTR(transition, "target"));
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
	for (int i = 0; i < allStates.size(); i++) {
		Element<std::string> state = Element<std::string>(allStates[i]);
		NodeSet<std::string> transitions = InterpreterImpl::filterChildElements(_nsInfo.xmlNSPrefix + "transition", state, false);

		transitions.to_document_order();

		for (int j = 1; j < transitions.size(); j++) {
			Element<std::string> transition = Element<std::string>(transitions[j]);
			for (int k = 0; k < j; k++) {
				Element<std::string> earlierTransition = Element<std::string>(transitions[k]);

				// will the earlier transition always be enabled when the later is?
				if (!HAS_ATTR(earlierTransition, "cond")) {
					// earlier transition has no condition -> check event descriptor
					if (!HAS_ATTR(earlierTransition, "event")) {
						// earlier transition is eventless
						issues.push_back(InterpreterIssue("Transition can never be optimally enabled", transition, InterpreterIssue::USCXML_ISSUE_INFO));
						goto NEXT_TRANSITION;

					} else if (HAS_ATTR(transition, "event")) {
						// does the earlier transition match all our events?
						std::list<std::string> events = InterpreterImpl::tokenizeIdRefs(ATTR(transition, "event"));

						bool allMatched = true;
						for (std::list<std::string>::iterator eventIter = events.begin(); eventIter != events.end(); eventIter++) {
							if (!InterpreterImpl::nameMatch(ATTR(earlierTransition, "event"), *eventIter)) {
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
        for (int i = 0; i < histories.size(); i++) {
            Element<std::string> history = Element<std::string>(histories[i]);
            if (!history.getParentNode() || history.getParentNode().getNodeType() != Node_base::ELEMENT_NODE)
                continue; // syntax check will have catched this
            Element<std::string> parent(history.getParentNode());
            if (InterpreterImpl::isAtomic(parent)) {
                issues.push_back(InterpreterIssue("Useless history '" + ATTR(history, "id") + "' in atomic state", history, InterpreterIssue::USCXML_ISSUE_INFO));
                continue;
            }
            std::list<std::set<Arabica::DOM::Element<std::string> > > configs = Complexity::getAllConfigurations(parent);
            if (configs.size() <= 1) {
                issues.push_back(InterpreterIssue("Useless history '" + ATTR(history, "id") + "' in state with single legal configuration", history, InterpreterIssue::USCXML_ISSUE_INFO));
                continue;
            }
        }
    }
    
	// check for valid initial attribute
	{
		NodeSet<std::string> withInitialAttr;
		withInitialAttr.push_back(allStates);
		withInitialAttr.push_back(_scxml);

		for (int i = 0; i < withInitialAttr.size(); i++) {
			Element<std::string> state = Element<std::string>(withInitialAttr[i]);

			if (HAS_ATTR(state, "initial")) {
                NodeSet<std::string> childs;
                childs.push_back(InterpreterImpl::filterChildElements(_nsInfo.xmlNSPrefix + "state", state, true));
                childs.push_back(InterpreterImpl::filterChildElements(_nsInfo.xmlNSPrefix + "parallel", state, true));
                childs.push_back(InterpreterImpl::filterChildElements(_nsInfo.xmlNSPrefix + "final", state, true));
                childs.push_back(InterpreterImpl::filterChildElements(_nsInfo.xmlNSPrefix + "history", state, true));

                std::list<std::string> intials = InterpreterImpl::tokenizeIdRefs(ATTR(state, "initial"));
				for (std::list<std::string>::iterator initIter = intials.begin(); initIter != intials.end(); initIter++) {
					if (seenStates.find(*initIter) == seenStates.end()) {
						issues.push_back(InterpreterIssue("Initial attribute has invalid target state with id '" + *initIter + "'", state, InterpreterIssue::USCXML_ISSUE_FATAL));
						continue;
					}
                    // value of the 'initial' attribute [..] must be descendants of the containing <state> or <parallel> element
                    if (!InterpreterImpl::isMember(seenStates[*initIter], childs)) {
                        issues.push_back(InterpreterIssue("Initial attribute references non-child state '" + *initIter + "'", state, InterpreterIssue::USCXML_ISSUE_FATAL));
                    }
				}
			}
		}
	}

    // check for legal configuration of target sets
    {
        std::map<Element<std::string>, std::string > targetIdSets;
        for (int i = 0; i < transitions.size(); i++) {
            Element<std::string> transition = Element<std::string>(transitions[i]);

            if (HAS_ATTR(transition, "target")) {
                targetIdSets[transition] = ATTR(transition, "target");
            }
        }
        
        for (int i = 0; i < initials.size(); i++) {
            Element<std::string> initial = Element<std::string>(initials[i]);

            if (HAS_ATTR(initial, "target")) {
                targetIdSets[initial] = ATTR(initial, "target");
            }
        }

        for (int i = 0; i < allStates.size(); i++) {
            Element<std::string> state = Element<std::string>(allStates[i]);
            
            if (HAS_ATTR(state, "initial")) {
                targetIdSets[state] = ATTR(state, "initial");
            }
        }

        for (std::map<Element<std::string>, std::string >::iterator setIter = targetIdSets.begin();
             setIter != targetIdSets.end();
             setIter++) {
            NodeSet<std::string> targets;
            std::list<std::string> targetIds = InterpreterImpl::tokenizeIdRefs(setIter->second);
            for (std::list<std::string>::iterator tgtIter = targetIds.begin(); tgtIter != targetIds.end(); tgtIter++) {
                if (seenStates.find(*tgtIter) == seenStates.end())
                    goto NEXT_SET;
                targets.push_back(seenStates[*tgtIter]);
            }
            if (!hasLegalCompletion(targets)) {
                issues.push_back(InterpreterIssue("Target states cause illegal configuration", setIter->first, InterpreterIssue::USCXML_ISSUE_FATAL));
            }
            NEXT_SET:;
        }
    }
    
    // check for valid initial transition
    {
        NodeSet<std::string> initTrans;
        initTrans.push_back(InterpreterImpl::filterChildElements(_nsInfo.xmlNSPrefix + "transition", initials, true));
        initTrans.push_back(InterpreterImpl::filterChildElements(_nsInfo.xmlNSPrefix + "transition", histories, true));

        for (int i = 0; i < initTrans.size(); i++) {
            Element<std::string> transition = Element<std::string>(initTrans[i]);
            
            /* In a conformant SCXML document, this transition must not contain 'cond' or 'event' attributes, and must specify a non-null 'target'
             * whose value is a valid state specification consisting solely of descendants of the containing state
             */
            
            if (HAS_ATTR(transition, "cond")) {
                issues.push_back(InterpreterIssue("Initial transition cannot have a condition", transition, InterpreterIssue::USCXML_ISSUE_FATAL));
            }
            if (HAS_ATTR(transition, "event")) {
                issues.push_back(InterpreterIssue("Initial transition cannot be eventful", transition, InterpreterIssue::USCXML_ISSUE_FATAL));
            }
            
            if (!transition.getParentNode() || !transition.getParentNode().getParentNode() || transition.getParentNode().getParentNode().getNodeType() != Node_base::ELEMENT_NODE)
                continue; // syntax will catch this one
            Element<std::string> state(transition.getParentNode().getParentNode());
            if (!InterpreterImpl::isState(state))
                continue; // syntax will catch this one

            NodeSet<std::string> childs;
            childs.push_back(InterpreterImpl::filterChildElements(_nsInfo.xmlNSPrefix + "state", state, true));
            childs.push_back(InterpreterImpl::filterChildElements(_nsInfo.xmlNSPrefix + "parallel", state, true));
            childs.push_back(InterpreterImpl::filterChildElements(_nsInfo.xmlNSPrefix + "final", state, true));
            childs.push_back(InterpreterImpl::filterChildElements(_nsInfo.xmlNSPrefix + "history", state, true));

            std::list<std::string> intials = InterpreterImpl::tokenizeIdRefs(ATTR(transition, "target"));
            for (std::list<std::string>::iterator initIter = intials.begin(); initIter != intials.end(); initIter++) {
                // the 'target' of a <transition> inside an <initial> or <history> element: all the states must be descendants of the containing <state> or <parallel> element
                if (!InterpreterImpl::isMember(seenStates[*initIter], childs)) {
                    issues.push_back(InterpreterIssue("Target of initial transition references non-child state '" + *initIter + "'", transition, InterpreterIssue::USCXML_ISSUE_FATAL));
                }
            }
        }
    }


	// check that all invokers exists
	{
		for (int i = 0; i < invokes.size(); i++) {
			Element<std::string> invoke = Element<std::string>(invokes[i]);
			if (HAS_ATTR(invoke, "type") && !_factory->hasInvoker(ATTR(invoke, "type"))) {
				// unknown at factory - adhoc extension?
				if (HAS_ATTR(invoke, "id") && interpreter->_invokers.find(ATTR(invoke, "id")) != interpreter->_invokers.end())
					continue; // not an issue

				IssueSeverity severity;
				if (HAS_ATTR(invoke, "idlocation")) {
					// we might still resolve at runtime
					severity = InterpreterIssue::USCXML_ISSUE_WARNING;
				} else {
					// fatality!
					severity = InterpreterIssue::USCXML_ISSUE_FATAL;
				}
				issues.push_back(InterpreterIssue("Invoke with unknown type '" + ATTR(invoke, "type") + "'", invoke, severity));
				continue;
			}
		}
	}

	// check that all io processors exists
	{
		for (int i = 0; i < sends.size(); i++) {
			Element<std::string> send = Element<std::string>(sends[i]);
			if (HAS_ATTR(send, "type") && !_factory->hasIOProcessor(ATTR(send, "type"))) {
				if (interpreter->_ioProcessors.find(ATTR(send, "type")) != interpreter->_ioProcessors.end())
					continue; // not an issue, available ad-hoc

				issues.push_back(InterpreterIssue("Send to unknown IO Processor '" + ATTR(send, "type") + "'", send, InterpreterIssue::USCXML_ISSUE_FATAL));
				continue;
			}
		}
	}

	// check that all custom executable content is known
	{
		NodeSet<std::string> allExecContentContainers;
		allExecContentContainers.push_back(onEntries);
		allExecContentContainers.push_back(onExits);
		allExecContentContainers.push_back(transitions);
		allExecContentContainers.push_back(finalizes);

		for (int i = 0; i < allExecContentContainers.size(); i++) {
			Element<std::string> block = Element<std::string>(allExecContentContainers[i]);
			NodeSet<std::string> execContents = InterpreterImpl::filterChildType(Node_base::ELEMENT_NODE, block);
			for (int j = 0; j < execContents.size(); j++) {
				Element<std::string> execContent = Element<std::string>(execContents[j]);
				// SCXML specific executable content, always available
				if (InterpreterImpl::isMember(execContent, allExecContents)) {
					continue;
				}
				if (!_factory->hasExecutableContent(execContent.getLocalName(), execContent.getNamespaceURI())) {
					issues.push_back(InterpreterIssue("Executable content element '" + execContent.getLocalName() + "' in namespace '" + execContent.getNamespaceURI() + "' unknown", execContent, InterpreterIssue::USCXML_ISSUE_FATAL));
					continue;
				}
			}
		}
	}

	// check that all SCXML elements have valid parents and required attributes
	{
		for (int i = 0; i < allElements.size(); i++) {
			Element<std::string> element = Element<std::string>(allElements[i]);
			std::string localName = LOCALNAME(element);
            
            if (reqAttr.find(localName) != reqAttr.end()) {
                for (std::set<std::string>::const_iterator reqIter = reqAttr[localName].begin();
                     reqIter != reqAttr[localName].end(); reqIter++) {
                    if (!HAS_ATTR(element, *reqIter)) {
                        issues.push_back(InterpreterIssue("Element " + localName + " is missing required attribute '" + *reqIter + "'", element, InterpreterIssue::USCXML_ISSUE_WARNING));
                    }
                }
            }
            
            if (localName == "scxml") // can be anywhere: <assign>, <content>, <other:embed>
                continue;
            
			if (!element.getParentNode() || element.getParentNode().getNodeType() != Node_base::ELEMENT_NODE) {
				issues.push_back(InterpreterIssue("Parent of " + localName + " is no element", element, InterpreterIssue::USCXML_ISSUE_WARNING));
				continue;
			}

			Element<std::string> parent = Element<std::string>(element.getParentNode());
			std::string parentName = LOCALNAME(parent);

			if (validParents[localName].find(parentName) == validParents[localName].end()) {
				issues.push_back(InterpreterIssue("Element " + localName + " can be no child of " + parentName, element, InterpreterIssue::USCXML_ISSUE_WARNING));
				continue;
			}
		}
	}

    // check attribute constraints
    {
        for (int i = 0; i < initials.size(); i++) {
            Element<std::string> initial = Element<std::string>(initials[i]);
            if (initial.getParentNode() && initial.getParentNode().getNodeType() == Node_base::ELEMENT_NODE) {
                Element<std::string> state(initial.getParentNode());
                if (HAS_ATTR(state, "initial")) {
                    issues.push_back(InterpreterIssue("State with initial attribute cannot have <initial> child ", state, InterpreterIssue::USCXML_ISSUE_WARNING));
                }
                if (InterpreterImpl::isAtomic(state)) {
                    issues.push_back(InterpreterIssue("Atomic state cannot have <initial> child ", state, InterpreterIssue::USCXML_ISSUE_WARNING));
                }
            }
        }
        for (int i = 0; i < allStates.size(); i++) {
            Element<std::string> state = Element<std::string>(allStates[i]);
            if (InterpreterImpl::isAtomic(state) && HAS_ATTR(state, "initial")) {
                issues.push_back(InterpreterIssue("Atomic state cannot have initial attribute ", state, InterpreterIssue::USCXML_ISSUE_WARNING));
            }
        }

        for (int i = 0; i < assigns.size(); i++) {
            Element<std::string> assign = Element<std::string>(assigns[i]);
            if (HAS_ATTR(assign, "expr") && assign.getChildNodes().getLength() > 0) {
                issues.push_back(InterpreterIssue("Assign element cannot have expr attribute and children", assign, InterpreterIssue::USCXML_ISSUE_WARNING));
            }
        }

        for (int i = 0; i < contents.size(); i++) {
            Element<std::string> content = Element<std::string>(contents[i]);
            if (HAS_ATTR(content, "expr") && content.getChildNodes().getLength() > 0) {
                issues.push_back(InterpreterIssue("Content element cannot have expr attribute and children", content, InterpreterIssue::USCXML_ISSUE_WARNING));
            }
        }

        for (int i = 0; i < params.size(); i++) {
            Element<std::string> param = Element<std::string>(params[i]);
            if (HAS_ATTR(param, "expr") && HAS_ATTR(param, "location")) {
                issues.push_back(InterpreterIssue("Param element cannot have both expr and location attribute", param, InterpreterIssue::USCXML_ISSUE_WARNING));
            }
        }

        for (int i = 0; i < scripts.size(); i++) {
            Element<std::string> script = Element<std::string>(scripts[i]);
            if (HAS_ATTR(script, "src") && script.getChildNodes().getLength() > 0) {
                issues.push_back(InterpreterIssue("Script element cannot have src attribute and children", script, InterpreterIssue::USCXML_ISSUE_WARNING));
            }
        }

        for (int i = 0; i < sends.size(); i++) {
            Element<std::string> send = Element<std::string>(sends[i]);
            if (HAS_ATTR(send, "event") && HAS_ATTR(send, "eventexpr")) {
                issues.push_back(InterpreterIssue("Send element cannot have both event and eventexpr attribute", send, InterpreterIssue::USCXML_ISSUE_WARNING));
            }
            if (HAS_ATTR(send, "target") && HAS_ATTR(send, "targetexpr")) {
                issues.push_back(InterpreterIssue("Send element cannot have both target and targetexpr attribute", send, InterpreterIssue::USCXML_ISSUE_WARNING));
            }
            if (HAS_ATTR(send, "type") && HAS_ATTR(send, "typeexpr")) {
                issues.push_back(InterpreterIssue("Send element cannot have both type and typeexpr attribute", send, InterpreterIssue::USCXML_ISSUE_WARNING));
            }
            if (HAS_ATTR(send, "id") && HAS_ATTR(send, "idlocation")) {
                issues.push_back(InterpreterIssue("Send element cannot have both id and idlocation attribute", send, InterpreterIssue::USCXML_ISSUE_WARNING));
            }
            if (HAS_ATTR(send, "delay") && HAS_ATTR(send, "delayexpr")) {
                issues.push_back(InterpreterIssue("Send element cannot have both delay and delayexpr attribute", send, InterpreterIssue::USCXML_ISSUE_WARNING));
            }
            if (HAS_ATTR(send, "delay") && HAS_ATTR(send, "target") && ATTR(send, "target")== "_internal") {
                issues.push_back(InterpreterIssue("Send element cannot have delay with target _internal", send, InterpreterIssue::USCXML_ISSUE_WARNING));
            }
            if (HAS_ATTR(send, "namelist") && InterpreterImpl::filterChildElements(_nsInfo.xmlNSPrefix + "content", send, false).size() > 0) {
                issues.push_back(InterpreterIssue("Send element cannot have namelist attribute and content child", send, InterpreterIssue::USCXML_ISSUE_WARNING));
            }
        }
        for (int i = 0; i < cancels.size(); i++) {
            Element<std::string> cancel = Element<std::string>(cancels[i]);
            if (HAS_ATTR(cancel, "sendid") && HAS_ATTR(cancel, "sendidexpr")) {
                issues.push_back(InterpreterIssue("Cancel element cannot have both sendid and eventexpr sendidexpr", cancel, InterpreterIssue::USCXML_ISSUE_WARNING));
            }
        }
        
        for (int i = 0; i < invokes.size(); i++) {
            Element<std::string> invoke = Element<std::string>(invokes[i]);
            if (HAS_ATTR(invoke, "type") && HAS_ATTR(invoke, "typeexpr")) {
                issues.push_back(InterpreterIssue("Invoke element cannot have both type and typeexpr attribute", invoke, InterpreterIssue::USCXML_ISSUE_WARNING));
            }
            if (HAS_ATTR(invoke, "src") && HAS_ATTR(invoke, "srcexpr")) {
                issues.push_back(InterpreterIssue("Invoke element cannot have both src and srcexpr attribute", invoke, InterpreterIssue::USCXML_ISSUE_WARNING));
            }
            if (HAS_ATTR(invoke, "id") && HAS_ATTR(invoke, "idlocation")) {
                issues.push_back(InterpreterIssue("Invoke element cannot have both id and idlocation attribute", invoke, InterpreterIssue::USCXML_ISSUE_WARNING));
            }
            if (HAS_ATTR(invoke, "namelist") && InterpreterImpl::filterChildElements(_nsInfo.xmlNSPrefix + "param", invoke, false).size() > 0) {
                issues.push_back(InterpreterIssue("Invoke element cannot have namelist attribute and param child", invoke, InterpreterIssue::USCXML_ISSUE_WARNING));
            }
        }

    }

	// check that the datamodel is known if not already instantiated
	if (!interpreter->_dataModel) {
		if (HAS_ATTR(_scxml, "datamodel")) {
			if (!_factory->hasDataModel(ATTR(_scxml, "datamodel"))) {
				issues.push_back(InterpreterIssue("SCXML document requires unknown datamodel '" + ATTR(_scxml, "datamodel") + "'", _scxml, InterpreterIssue::USCXML_ISSUE_FATAL));

				// we cannot even check the rest as we require a datamodel
				return issues;
			}
		}
	}

	bool instantiatedDataModel = false;
	// instantiate datamodel if not explicitly set
	if (!_dataModel) {
		if (HAS_ATTR(_scxml, "datamodel")) {
			// might throw
			_dataModel = _factory->createDataModel(ATTR(_scxml, "datamodel"), interpreter);
			instantiatedDataModel = true;
		} else {
			_dataModel = _factory->createDataModel("null", interpreter);
		}
	}


	// test all scripts for valid syntax
	{
		for (int i = 0; i < scripts.size(); i++) {
			Element<std::string> script = Element<std::string>(scripts[i]);

			if (script.hasChildNodes()) {
				// search for the text node with the actual script
				std::string scriptContent;
				for (Node<std::string> child = script.getFirstChild(); child; child = child.getNextSibling()) {
					if (child.getNodeType() == Node_base::TEXT_NODE || child.getNodeType() == Node_base::CDATA_SECTION_NODE)
						scriptContent += child.getNodeValue();
				}

				if (!_dataModel.isValidSyntax(scriptContent)) {
					issues.push_back(InterpreterIssue("Syntax error in script", script, InterpreterIssue::USCXML_ISSUE_WARNING));
				}
			}
		}
	}

	// test the various attributes with datamodel expressions for valid syntax
	{
		NodeSet<std::string> withCondAttrs;
		withCondAttrs.push_back(transitions);
		withCondAttrs.push_back(ifs);
		withCondAttrs.push_back(elseIfs);

		for (int i = 0; i < withCondAttrs.size(); i++) {
			Element<std::string> condAttr = Element<std::string>(withCondAttrs[i]);
			if (HAS_ATTR(condAttr, "cond")) {
				if (!_dataModel.isValidSyntax(ATTR(condAttr, "cond"))) {
					issues.push_back(InterpreterIssue("Syntax error in cond attribute", condAttr, InterpreterIssue::USCXML_ISSUE_WARNING));
					continue;
				}
			}
		}
	}

	{
		NodeSet<std::string> withExprAttrs;
		withExprAttrs.push_back(logs);
		withExprAttrs.push_back(datas);
		withExprAttrs.push_back(assigns);
		withExprAttrs.push_back(contents);
		withExprAttrs.push_back(params);

		for (int i = 0; i < withExprAttrs.size(); i++) {
			Element<std::string> withExprAttr = Element<std::string>(withExprAttrs[i]);
			if (HAS_ATTR(withExprAttr, "expr")) {
				if (InterpreterImpl::isMember(withExprAttr, datas) || InterpreterImpl::isMember(withExprAttr, assigns)) {
					if (!_dataModel.isValidSyntax("foo = " + ATTR(withExprAttr, "expr"))) { // TODO: this is ECMAScripty!
						issues.push_back(InterpreterIssue("Syntax error in expr attribute", withExprAttr, InterpreterIssue::USCXML_ISSUE_WARNING));
						continue;
					}
				} else {
					if (!_dataModel.isValidSyntax(ATTR(withExprAttr, "expr"))) {
						issues.push_back(InterpreterIssue("Syntax error in expr attribute", withExprAttr, InterpreterIssue::USCXML_ISSUE_WARNING));
						continue;
					}
				}
			}
		}
	}

	{
		for (int i = 0; i < foreachs.size(); i++) {
			Element<std::string> foreach = Element<std::string>(foreachs[i]);
			if (HAS_ATTR(foreach, "array")) {
				if (!_dataModel.isValidSyntax(ATTR(foreach, "array"))) {
					issues.push_back(InterpreterIssue("Syntax error in array attribute", foreach, InterpreterIssue::USCXML_ISSUE_WARNING));
				}
			}
			if (HAS_ATTR(foreach, "item")) {
				if (!_dataModel.isValidSyntax(ATTR(foreach, "item"))) {
					issues.push_back(InterpreterIssue("Syntax error in item attribute", foreach, InterpreterIssue::USCXML_ISSUE_WARNING));
				}
			}
			if (HAS_ATTR(foreach, "index")) {
				if (!_dataModel.isValidSyntax(ATTR(foreach, "index"))) {
					issues.push_back(InterpreterIssue("Syntax error in index attribute", foreach, InterpreterIssue::USCXML_ISSUE_WARNING));
				}
			}
		}
	}

	{
		for (int i = 0; i < sends.size(); i++) {
			Element<std::string> send = Element<std::string>(sends[i]);
			if (HAS_ATTR(send, "eventexpr")) {
				if (!_dataModel.isValidSyntax(ATTR(send, "eventexpr"))) {
					issues.push_back(InterpreterIssue("Syntax error in eventexpr attribute", send, InterpreterIssue::USCXML_ISSUE_WARNING));
				}
			}
			if (HAS_ATTR(send, "targetexpr")) {
				if (!_dataModel.isValidSyntax(ATTR(send, "targetexpr"))) {
					issues.push_back(InterpreterIssue("Syntax error in targetexpr attribute", send, InterpreterIssue::USCXML_ISSUE_WARNING));
				}
			}
			if (HAS_ATTR(send, "typeexpr")) {
				if (!_dataModel.isValidSyntax(ATTR(send, "typeexpr"))) {
					issues.push_back(InterpreterIssue("Syntax error in typeexpr attribute", send, InterpreterIssue::USCXML_ISSUE_WARNING));
				}
			}
			if (HAS_ATTR(send, "idlocation")) {
				if (!_dataModel.isValidSyntax(ATTR(send, "idlocation"))) {
					issues.push_back(InterpreterIssue("Syntax error in idlocation attribute", send, InterpreterIssue::USCXML_ISSUE_WARNING));
				}
			}
			if (HAS_ATTR(send, "delayexpr")) {
				if (!_dataModel.isValidSyntax(ATTR(send, "delayexpr"))) {
					issues.push_back(InterpreterIssue("Syntax error in delayexpr attribute", send, InterpreterIssue::USCXML_ISSUE_WARNING));
				}
			}
		}

	}

	{
		for (int i = 0; i < invokes.size(); i++) {
			Element<std::string> invoke = Element<std::string>(invokes[i]);
			if (HAS_ATTR(invoke, "typeexpr")) {
				if (!_dataModel.isValidSyntax(ATTR(invoke, "typeexpr"))) {
					issues.push_back(InterpreterIssue("Syntax error in typeexpr attribute", invoke, InterpreterIssue::USCXML_ISSUE_WARNING));
					continue;
				}
			}
			if (HAS_ATTR(invoke, "srcexpr")) {
				if (!_dataModel.isValidSyntax(ATTR(invoke, "srcexpr"))) {
					issues.push_back(InterpreterIssue("Syntax error in srcexpr attribute", invoke, InterpreterIssue::USCXML_ISSUE_WARNING));
					continue;
				}
			}
			if (HAS_ATTR(invoke, "idlocation")) {
				if (!_dataModel.isValidSyntax(ATTR(invoke, "idlocation"))) {
					issues.push_back(InterpreterIssue("Syntax error in idlocation attribute", invoke, InterpreterIssue::USCXML_ISSUE_WARNING));
					continue;
				}
			}
		}
	}

	{
		for (int i = 0; i < cancels.size(); i++) {
			Element<std::string> cancel = Element<std::string>(cancels[i]);
			if (HAS_ATTR(cancel, "sendidexpr")) {
				if (!_dataModel.isValidSyntax(ATTR(cancel, "sendidexpr"))) {
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


}