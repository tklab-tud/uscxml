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

#include "uscxml/Common.h"

#include <string>
#include <list>
#include <xercesc/dom/DOM.hpp>
#include "uscxml/util/DOM.h"
#include "uscxml/util/Convenience.h"

// forward declare
namespace XERCESC_NS {
class DOMElement;
class DOMNode;
}


namespace uscxml {

// see braindead declspec syntax here: https://msdn.microsoft.com/en-us/library/aa273692(v=vs.60).aspx

std::list<XERCESC_NS::DOMElement*> USCXML_API getChildStates(
    const XERCESC_NS::DOMElement* state,
    bool properOnly = true);

std::list<XERCESC_NS::DOMElement*> USCXML_API getChildStates(
    const std::list<XERCESC_NS::DOMElement*>& states,
    bool properOnly = true);

XERCESC_NS::DOMElement USCXML_API *getParentState(const XERCESC_NS::DOMElement* element);
XERCESC_NS::DOMElement USCXML_API *getSourceState(const XERCESC_NS::DOMElement* transition);
XERCESC_NS::DOMElement USCXML_API *findLCCA(const std::list<XERCESC_NS::DOMElement*>& states);

std::list<XERCESC_NS::DOMElement*> USCXML_API getProperAncestors(
    const XERCESC_NS::DOMElement* s1,
    const XERCESC_NS::DOMElement* s2);

std::list<XERCESC_NS::DOMElement*> USCXML_API getTargetStates(
    const XERCESC_NS::DOMElement* transition,
    const XERCESC_NS::DOMElement* root);

std::list<XERCESC_NS::DOMElement*> USCXML_API getEffectiveTargetStates(const XERCESC_NS::DOMElement* transition);

XERCESC_NS::DOMElement USCXML_API *getTransitionDomain(
    const XERCESC_NS::DOMElement* transition,
    const XERCESC_NS::DOMElement* root);

bool USCXML_API areFromSameMachine(const XERCESC_NS::DOMNode* n1,
                                   const XERCESC_NS::DOMNode* n2);

std::list<XERCESC_NS::DOMElement*> USCXML_API getStates(
    const std::list<std::string>& stateIds,
    const XERCESC_NS::DOMElement* root);

XERCESC_NS::DOMElement USCXML_API *getState(
    const std::string& stateId,
    const XERCESC_NS::DOMElement* root);

std::list<XERCESC_NS::DOMElement*> USCXML_API getInitialStates(
    const XERCESC_NS::DOMElement* state,
    const XERCESC_NS::DOMElement* root);

std::list<XERCESC_NS::DOMElement*> USCXML_API getReachableStates(const XERCESC_NS::DOMElement* root);
std::list<XERCESC_NS::DOMElement*> USCXML_API getExitSet(
    const XERCESC_NS::DOMElement* transition,
    const XERCESC_NS::DOMElement* root);

bool USCXML_API conflicts(const XERCESC_NS::DOMElement* transition1,
                          const XERCESC_NS::DOMElement* transition2,
                          const XERCESC_NS::DOMElement* root);

bool USCXML_API isState(const XERCESC_NS::DOMElement* state, bool properOnly = true);
bool USCXML_API isCompound(const XERCESC_NS::DOMElement* state);
bool USCXML_API isAtomic(const XERCESC_NS::DOMElement* state);
bool USCXML_API isParallel(const XERCESC_NS::DOMElement* state);
bool USCXML_API isFinal(const XERCESC_NS::DOMElement* state);
bool USCXML_API isHistory(const XERCESC_NS::DOMElement* state);

}

#endif /* end of include guard: PREDICATES_H_D3A20484 */
