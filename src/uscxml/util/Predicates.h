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

#ifndef PREDICATES_H_D3A20484
#define PREDICATES_H_D3A20484

#include <string>
#include <list>
#include <xercesc/dom/DOM.hpp>
#include "uscxml/util/DOM.h"
#include "uscxml/util/Convenience.h"

namespace uscxml {

std::list<XERCESC_NS::DOMElement*> getChildStates(const XERCESC_NS::DOMElement* state, bool properOnly = true);
std::list<XERCESC_NS::DOMElement*> getChildStates(const std::list<XERCESC_NS::DOMElement*>& states, bool properOnly = true);
XERCESC_NS::DOMElement* getParentState(const XERCESC_NS::DOMElement* element);
XERCESC_NS::DOMElement* getSourceState(const XERCESC_NS::DOMElement* transition);
XERCESC_NS::DOMElement* findLCCA(const std::list<XERCESC_NS::DOMElement*>& states);
std::list<XERCESC_NS::DOMElement*> getProperAncestors(const XERCESC_NS::DOMElement* s1, const XERCESC_NS::DOMElement* s2);

std::list<XERCESC_NS::DOMElement*> getTargetStates(const XERCESC_NS::DOMElement* transition, const XERCESC_NS::DOMElement* root);
std::list<XERCESC_NS::DOMElement*> getEffectiveTargetStates(const XERCESC_NS::DOMElement* transition);
XERCESC_NS::DOMElement* getTransitionDomain(const XERCESC_NS::DOMElement* transition, const XERCESC_NS::DOMElement* root);

bool areFromSameMachine(const XERCESC_NS::DOMNode* n1, const XERCESC_NS::DOMNode* n2);

std::list<XERCESC_NS::DOMElement*> getStates(const std::list<std::string>& stateIds, const XERCESC_NS::DOMElement* root);
XERCESC_NS::DOMElement* getState(const std::string& stateId, const XERCESC_NS::DOMElement* root);
std::list<XERCESC_NS::DOMElement*> getInitialStates(const XERCESC_NS::DOMElement* state, const XERCESC_NS::DOMElement* root);
std::list<XERCESC_NS::DOMElement*> getReachableStates(const XERCESC_NS::DOMElement* root);
std::list<XERCESC_NS::DOMElement*> getExitSet(const XERCESC_NS::DOMElement* transition, const XERCESC_NS::DOMElement* root);
bool conflicts(const XERCESC_NS::DOMElement* transition1, const XERCESC_NS::DOMElement* transition2, const XERCESC_NS::DOMElement* root);

bool isState(const XERCESC_NS::DOMElement* state, bool properOnly = true);
bool isCompound(const XERCESC_NS::DOMElement* state);
bool isAtomic(const XERCESC_NS::DOMElement* state);
bool isParallel(const XERCESC_NS::DOMElement* state);
bool isFinal(const XERCESC_NS::DOMElement* state);
bool isHistory(const XERCESC_NS::DOMElement* state);


}

#endif /* end of include guard: PREDICATES_H_D3A20484 */
