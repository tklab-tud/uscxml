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

std::list<xercesc::DOMElement*> getChildStates(const xercesc::DOMElement* state, bool properOnly = true);
std::list<xercesc::DOMElement*> getChildStates(const std::list<xercesc::DOMElement*>& states, bool properOnly = true);
xercesc::DOMElement* getParentState(const xercesc::DOMElement* element);
xercesc::DOMElement* getSourceState(const xercesc::DOMElement* transition);
xercesc::DOMElement* findLCCA(const std::list<xercesc::DOMElement*>& states);
std::list<xercesc::DOMElement*> getProperAncestors(const xercesc::DOMElement* s1, const xercesc::DOMElement* s2);

std::list<xercesc::DOMElement*> getTargetStates(const xercesc::DOMElement* transition, const xercesc::DOMElement* root);
std::list<xercesc::DOMElement*> getEffectiveTargetStates(const xercesc::DOMElement* transition);
xercesc::DOMElement* getTransitionDomain(const xercesc::DOMElement* transition, const xercesc::DOMElement* root);

bool isInEmbeddedDocument(const xercesc::DOMNode* node);

std::list<xercesc::DOMElement*> getStates(const std::list<std::string>& stateIds, const xercesc::DOMElement* root);
xercesc::DOMElement* getState(const std::string& stateId, const xercesc::DOMElement* root);
std::list<xercesc::DOMElement*> getInitialStates(const xercesc::DOMElement* state, const xercesc::DOMElement* root);
std::list<xercesc::DOMElement*> getReachableStates(const xercesc::DOMElement* root);
std::list<xercesc::DOMElement*> getExitSet(const xercesc::DOMElement* transition, const xercesc::DOMElement* root);
bool conflicts(const xercesc::DOMElement* transition1, const xercesc::DOMElement* transition2, const xercesc::DOMElement* root);

bool isState(const xercesc::DOMElement* state, bool properOnly = true);
bool isCompound(const xercesc::DOMElement* state);
bool isAtomic(const xercesc::DOMElement* state);
bool isParallel(const xercesc::DOMElement* state);
bool isFinal(const xercesc::DOMElement* state);
bool isHistory(const xercesc::DOMElement* state);


}

#endif /* end of include guard: PREDICATES_H_D3A20484 */
