/**
 *  @file
 *  @author     2016 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#include "Predicates.h"
#include "uscxml/util/String.h"

namespace uscxml {

using namespace XERCESC_NS;

std::list<DOMElement*> getChildStates(const DOMElement* state, bool properOnly) {
	std::list<DOMElement*> children;

    for (auto childElem = state->getFirstElementChild(); childElem; childElem = childElem->getNextElementSibling()) {
		if (isState(childElem, properOnly)) {
			children.push_back(childElem);
		}
	}
	return children;
}

std::list<XERCESC_NS::DOMElement*> getChildStates(const std::list<XERCESC_NS::DOMElement*>& states, bool properOnly) {
	std::list<XERCESC_NS::DOMElement*>  children;
	for (auto stateIter = states.begin(); stateIter != states.end(); stateIter++) {
		std::list<DOMElement*> tmp = getChildStates(*stateIter, properOnly);
		children.merge(tmp);
	}
	return children;
}


DOMElement* getParentState(const DOMElement* element) {
	DOMNode* parent = element->getParentNode();
	while(parent && !isState(dynamic_cast<DOMElement*>(parent))) {
		parent = parent->getParentNode();
	}
	return dynamic_cast<DOMElement*>(parent);
}

DOMElement* getSourceState(const DOMElement* transition) {
	if (iequals(TAGNAME_CAST(transition->getParentNode()), XML_PREFIX(transition).str() + "initial"))
		return dynamic_cast<DOMElement*>(transition->getParentNode()->getParentNode());
	return dynamic_cast<DOMElement*>(transition->getParentNode());
}


/**
 See: http://www.w3.org/TR/scxml/#LCCA
 The Least Common Compound Ancestor is the <state> or <scxml> element s such that s is a proper ancestor
 of all states on stateList and no descendant of s has this property. Note that there is guaranteed to be
 such an element since the <scxml> wrapper element is a common ancestor of all states. Note also that since
 we are speaking of proper ancestor (parent or parent of a parent, etc.) the LCCA is never a member of stateList.
 */

#define VERBOSE_FIND_LCCA 0
DOMElement* findLCCA(const std::list<DOMElement*>& states) {
    
	std::list<DOMElement*> ancestors = getProperAncestors(states.front(), NULL);
	DOMElement* ancestor = NULL;

#if VERBOSE_FIND_LCCA
    std::cout << "states:    " << states.size() << std::endl;
    std::cout << "front:     " << DOMUtils::xPathForNode(states.front()) << std::endl;
    std::cout << "ancestors: " << ancestors.size() << std::endl;
#endif

	for (auto ancIter = ancestors.begin(); ancIter != ancestors.end(); ancIter++) {
		if (!isCompound(dynamic_cast<DOMElement*>(*ancIter)))
			continue;
		for (auto stateIter = states.begin(); stateIter != states.end(); stateIter++) {

#if VERBOSE_FIND_LCCA
			std::cerr << "Checking " << ATTR_CAST(*stateIter, "id") << " and " << ATTR_CAST(*ancIter, "id") << std::endl;
#endif

			if (!DOMUtils::isDescendant(*stateIter, *ancIter))
				goto NEXT_ANCESTOR;
		}
		ancestor = *ancIter;
		break;
NEXT_ANCESTOR:
		;
	}

	// take uppermost root as ancestor
	if (!ancestor && ancestors.size() > 0)
		ancestor = ancestors.back();

#if VERBOSE_FIND_LCCA
	std::cerr << " -> " << ATTR_CAST(ancestor, "id") << " " << ancestor->getLocalName() << std::endl;
#endif
	return ancestor;
}

/*
 * If state2 is null, returns the set of all ancestors of state1 in ancestry order
 * (state1's parent followed by the parent's parent, etc. up to an including the <scxml>
 * element). If state2 is non-null, returns in ancestry order the set of all ancestors
 * of state1, up to but not including state2. (A "proper ancestor" of a state is its
 * parent, or the parent's parent, or the parent's parent's parent, etc.))If state2 is
 * state1's parent, or equal to state1, or a descendant of state1, this returns the empty set.
 */

std::list<DOMElement*> getProperAncestors(const DOMElement* s1, const DOMElement* s2) {

	std::list<DOMElement*> ancestors;
	if (isState(s1, false)) {
        // is it correct to also consider pseudo-states?
        // gcc bug in findLCCA with test387, test388, test579, test580 otherwise
		DOMNode* node = (DOMNode*)s1;
		while((node = node->getParentNode())) {
			if (node->getNodeType() != DOMNode::ELEMENT_NODE)
				break;

			const DOMElement* nodeElem = dynamic_cast<const DOMElement*>(node);
			if (!isState(nodeElem))
				break;

			if (!iequals(LOCALNAME(nodeElem), "parallel") &&
                !iequals(LOCALNAME(nodeElem), "state") &&
                !iequals(LOCALNAME(nodeElem), "scxml"))
				break;
			if (node == s2)
				break;
			ancestors.push_back(dynamic_cast<DOMElement*>(node));
		}
	}
	return ancestors;
}

std::list<DOMElement*> getExitSet(const DOMElement* transition, const DOMElement* root) {
	std::list<DOMElement*> statesToExit;
	if (HAS_ATTR(transition, "target")) {
		DOMElement* domain = getTransitionDomain(transition, root);
		if (domain == NULL)
			return statesToExit;

//        std::cout << "transition: " << DOMUtils::xPathForNode(transition) << std::endl;
//        std::cout << "domain:     " << DOMUtils::xPathForNode(domain) << std::endl;

		std::set<std::string> elements;
		elements.insert(XML_PREFIX(transition).str() + "parallel");
		elements.insert(XML_PREFIX(transition).str() + "state");
		elements.insert(XML_PREFIX(transition).str() + "final");
		statesToExit = DOMUtils::inDocumentOrder(elements, domain);

		if (statesToExit.front() == domain) {
			statesToExit.pop_front(); // do not include domain itself
		}
//        std::cout << "OK" << std::endl;

	}

	return statesToExit;
}

bool conflicts(const DOMElement* t1, const DOMElement* t2, const DOMElement* root) {
	return (
            (getSourceState(t1) == getSourceState(t2)) ||
	        (DOMUtils::isDescendant(getSourceState(t1), getSourceState(t2))) ||
	        (DOMUtils::isDescendant(getSourceState(t2), getSourceState(t1))) ||
            (DOMUtils::hasIntersection(getExitSet(t1, root), getExitSet(t2, root)))
           );
}

bool isState(const DOMElement* state, bool properOnly) {
	if (!state)
		return false;

	std::string localName = LOCALNAME(state);
	if (iequals("state", localName))
		return true;
	if (iequals("scxml", localName))
		return true;
	if (iequals("parallel", localName))
		return true;
	if (iequals("final", localName))
		return true;
	if (properOnly)
		return false;

	if (iequals("history", localName))
		return true;
	if (iequals("initial", localName))
		return true;

	return false;
}

bool isFinal(const DOMElement* state) {
	std::string localName = LOCALNAME(state);
	if (iequals("final", localName))
		return true;
	if (HAS_ATTR(state, "final") && iequals("true", ATTR(state, "final")))
		return true;
	return false;
}

bool isAtomic(const DOMElement* state) {
	if (!isState(state))
		return false;

	if (iequals("final", LOCALNAME(state)))
		return true;

	if (iequals("parallel", LOCALNAME(state)))
		return false;

	if (getChildStates(state).size() > 0)
		return false;

	return true;
}

bool isHistory(const DOMElement* state) {
	if (iequals("history", LOCALNAME(state)))
		return true;
	return false;
}

bool isParallel(const DOMElement* state) {
	if (!isState(state))
		return false;
	if (iequals("parallel", LOCALNAME(state)))
		return true;
	return false;
}


bool isCompound(const DOMElement* state) {
	if (!isState(state))
		return false;

	if (iequals(LOCALNAME(state), "parallel")) // parallel is no compound state
		return false;

	if (getChildStates(state).size() > 0)
		return true;

	return false;
}

std::list<DOMElement*> getTargetStates(const DOMElement* transition, const DOMElement* root) {
	std::list<DOMElement*> targetStates;

	std::string targetId = ATTR(transition, "target");
	std::list<std::string> targetIds = tokenize(ATTR(transition, "target"));

	for (auto targetIter = targetIds.begin(); targetIter != targetIds.end(); targetIter++) {
		DOMElement* state = getState(*targetIter, root);
		if (state) {
			targetStates.push_back(state);
		}
	}
	return targetStates;
}


DOMElement* getTransitionDomain(const DOMElement* transition, const DOMElement* root) {
	std::list<DOMElement*> tStates = getTargetStates(transition, root);
	if (tStates.size() == 0) {
		return NULL;
	}
	std::string transitionType = (HAS_ATTR(transition, "type") ? ATTR(transition, "type") : "external");
	DOMElement* source = getSourceState(transition);

	if (iequals(transitionType, "internal") && isCompound(source)) {
		for (auto tIter = tStates.begin(); tIter != tStates.end(); tIter++) {
			if (!DOMUtils::isDescendant(*tIter, source))
				goto BREAK_LOOP;
		}
		return source;
	}

BREAK_LOOP:
	tStates.push_front(source);
    
	return findLCCA(tStates);
}

std::list<DOMElement*> getStates(const std::list<std::string>& stateIds, const DOMElement* root) {
	std::list<DOMElement*> states;
	std::list<std::string>::const_iterator tokenIter = stateIds.begin();
	while(tokenIter != stateIds.end()) {
		states.push_back(getState(*tokenIter, root));
		tokenIter++;
	}
	return states;
}

DOMElement* getState(const std::string& stateId, const DOMElement* root) {

	std::list<const DOMElement*> stateStack;
	stateStack.push_back(root);

	while(stateStack.size() > 0) {
		const DOMElement* curr = stateStack.front();
		stateStack.pop_front();

		if (!isState(curr, false))
			assert(false);

//        std::cout << *curr;

		if (HAS_ATTR(curr, "id") && ATTR(curr, "id") == stateId)
			return (DOMElement*)curr;

		std::list<DOMElement*> children = getChildStates(curr, false);
		stateStack.insert(stateStack.end(), children.begin(), children.end());
	}

	return NULL;
}

/**
 * In a conformant SCXML document, a compound state may specify either an "initial"
 * attribute or an <initial> element, but not both. See 3.6 <initial> for a
 * discussion of the difference between the two notations. If neither the "initial"
 * attribute nor an <initial> element is specified, the SCXML Processor must use
 * the first child state in document order as the default initial state.
 */
std::list<DOMElement*> getInitialStates(const DOMElement* state, const DOMElement* root) {
	if (!state) {
		state = root;
	}

#if VERBOSE
	std::cerr << "Getting initial state of " << TAGNAME(state) << " " << ATTR(state, "id") << std::endl;
#endif

	if (isAtomic(state)) {
		return std::list<DOMElement*>();
	}

	if (isParallel(state)) {
		return getChildStates(state);
	}

	if (isCompound(state)) {
		// initial attribute at element
		if (HAS_ATTR(state, "initial")) {
			return getStates(tokenize(ATTR(state, "initial")), root);
		}

		// initial element as child
		std::list<DOMElement*> initElems = DOMUtils::filterChildElements(XML_PREFIX(state).str() + "initial", state);
		if(initElems.size() > 0 ) {
			std::list<DOMElement*> initTrans = DOMUtils::filterChildElements(XML_PREFIX(initElems.front()).str() + "transition", initElems.front());
			if (initTrans.size() > 0 && HAS_ATTR(initTrans.front(),"target")) {
				return getTargetStates(initTrans.front(), root);
			}
			return std::list<DOMElement*>();
		}

		// first child state
		std::list<DOMElement*> initStates;
        for (auto childElem = state->getFirstElementChild(); childElem; childElem = childElem->getNextElementSibling()) {
			if (isState(childElem)) {
				initStates.push_back(childElem);
				return initStates;
			}
		}
	}

	// nothing found
	return std::list<DOMElement*>();
}

std::list<DOMElement*> getReachableStates(const DOMElement* root) {
	/** Check which states are reachable */

	std::list<DOMElement*> reachable; // total transitive hull
	std::list<DOMElement*> additions; // nodes added in last iteration
	std::list<DOMElement*> current; // new nodes caused by nodes added
	additions.push_back((DOMElement*)root);

	while (additions.size() > 0) {

#if 0
		for (auto stateIter = additions.begin(); stateIter != additions.end(); stateIter++) {
			DOMElement* state = *stateIter;
			std::cout << (HAS_ATTR(state, "id") ? ATTR(state, "id") : (std::string)X(state->getLocalName())) << ", " << std::endl;
		}
#endif
		// reachable per initial attribute or document order - size will increase as we append new states
		for (auto stateIter = additions.begin(); stateIter != additions.end(); stateIter++) {
			// get the state's initial states
			DOMElement* state = *stateIter;
			std::list<DOMElement*> initials = getInitialStates(state, root);
			for (auto initIter = initials.begin(); initIter != initials.end(); initIter++) {
				DOMElement* initial = *initIter;
				if (!DOMUtils::isMember(initial, additions) && !DOMUtils::isMember(initial, reachable)) {
					current.push_back(initial);
				}
			}
		}

		// reachable per target attribute in transitions
		for (auto stateIter = additions.begin(); stateIter != additions.end(); stateIter++) {
			DOMElement* state = *stateIter;
			std::list<DOMElement*> transitions = DOMUtils::filterChildElements(XML_PREFIX(state).str() + "transition", state, false);
			for (auto transIter = transitions.begin(); transIter != transitions.end(); transIter++) {
				DOMElement* transition = *transIter;
				std::list<DOMElement*> targets = getTargetStates(transition, root);
				for (auto targetIter = targets.begin(); targetIter != targets.end(); targetIter++) {
					DOMElement* target = *targetIter;
					if (!DOMUtils::isMember(target, additions) && !DOMUtils::isMember(target, reachable)) {
						current.push_back(target);
					}
				}
			}
		}

		// reachable via a reachable child state
		for (auto stateIter = additions.begin(); stateIter != additions.end(); stateIter++) {
			DOMElement* state = *stateIter;
			if (isAtomic(state)) {
				// iterate the states parents
				DOMNode* parent = state->getParentNode();
				while(parent && parent->getNodeType() == DOMNode::ELEMENT_NODE) {
					DOMElement* parentElem = static_cast<DOMElement*>(parent);
					if (!isState(parentElem)) {
						break;
					}
					if (!DOMUtils::isMember(parentElem, additions) && !DOMUtils::isMember(parentElem, reachable)) {
						current.push_back(parentElem);
					}
					parent = parent->getParentNode();
				}
			}
		}

		// add all additions from last iterations to reachable set
		reachable.insert(reachable.end(), additions.begin(), additions.end());

		// set current additions as new additions
		additions = current;

		// clear current set for next iteration
		current.clear();
	}

	return reachable;
}


bool areFromSameMachine(const DOMNode* n1, const DOMNode* n2) {
    // we traverse each nodes parent's until we reach an scxml element or null
	const DOMNode* p1 = n1;
	while(p1) {
		if(iequals(LOCALNAME(p1), "scxml")) {
            break;
		}
		p1 = p1->getParentNode();
	}

    const DOMNode* p2 = n2;
    while(p2) {
        if(iequals(LOCALNAME(p2), "scxml")) {
            break;
        }
        p2 = p2->getParentNode();
    }

    return p1 == p2;
}

}