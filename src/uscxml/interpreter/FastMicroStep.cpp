/**
 *  @file
 *  @author     2012-2016 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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


#include "uscxml/config.h"
#include "FastMicroStep.h"
#include "uscxml/util/DOM.h"
#include "uscxml/util/String.h"
#include "uscxml/util/Base64.hpp"
#include "uscxml/util/Predicates.h"
#include "uscxml/util/Convenience.h"
#include "uscxml/interpreter/InterpreterMonitor.h"

#include "uscxml/interpreter/Logging.h"

#include <stdlib.h> // strtol

#undef USCXML_VERBOSE
#undef WITH_CACHE_FILES

#define BIT_ANY_SET(b) (!b.none())
#define BIT_HAS(idx, bitset) (bitset[idx])
#define BIT_HAS_AND(bitset1, bitset2) bitset1.intersects(bitset2)
#define BIT_SET_AT(idx, bitset) bitset[idx] = true;
#define BIT_CLEAR(idx, bitset) bitset[idx] = false;

#define USCXML_GET_TRANS(i) (*_transitions[i])
#define USCXML_GET_STATE(i) (*_states[i])

#define USCXML_CTX_PRISTINE           0x00
#define USCXML_CTX_SPONTANEOUS        0x01
#define USCXML_CTX_INITIALIZED        0x02
#define USCXML_CTX_TOP_LEVEL_FINAL    0x04
#define USCXML_CTX_TRANSITION_FOUND   0x08
#define USCXML_CTX_FINISHED           0x10
#define USCXML_CTX_STABLE             0x20 // only needed to signal onStable once

#define USCXML_TRANS_SPONTANEOUS      0x01
#define USCXML_TRANS_TARGETLESS       0x02
#define USCXML_TRANS_INTERNAL         0x04
#define USCXML_TRANS_HISTORY          0x08
#define USCXML_TRANS_INITIAL          0x10

#define USCXML_STATE_ATOMIC           0x01
#define USCXML_STATE_PARALLEL         0x02
#define USCXML_STATE_COMPOUND         0x03
#define USCXML_STATE_FINAL            0x04
#define USCXML_STATE_HISTORY_DEEP     0x05
#define USCXML_STATE_HISTORY_SHALLOW  0x06
#define USCXML_STATE_INITIAL          0x07
#define USCXML_STATE_HAS_HISTORY      0x80  /* highest bit */
#define USCXML_STATE_MASK(t)     (t & 0x7F) /* mask highest bit */

#define USCXML_NUMBER_STATES _states.size()
#define USCXML_NUMBER_TRANS _transitions.size()

#ifdef __GNUC__
#  define likely(x)       (__builtin_expect(!!(x), 1))
#  define unlikely(x)     (__builtin_expect(!!(x), 0))
#else
#  define likely(x)       (x)
#  define unlikely(x)     (x)
#endif

namespace uscxml {

using namespace XERCESC_NS;

FastMicroStep::FastMicroStep(MicroStepCallbacks* callbacks)
	: MicroStepImpl(callbacks), _flags(USCXML_CTX_PRISTINE), _isInitialized(false), _isCancelled(false) {
}

FastMicroStep::~FastMicroStep() {
	for (size_t i = 0; i < _states.size(); i++) {
		delete(_states[i]);
	}
	for (size_t i = 0; i < _transitions.size(); i++) {
		delete(_transitions[i]);
	}
}

std::shared_ptr<MicroStepImpl> FastMicroStep::create(MicroStepCallbacks* callbacks) {
	return std::shared_ptr<MicroStepImpl>(new FastMicroStep(callbacks));
}

void FastMicroStep::deserialize(const Data& encodedState) {
	if (!encodedState.hasKey("configuration") ||
	        !encodedState.hasKey("invocations") ||
	        !encodedState.hasKey("histories") ||
	        !encodedState.hasKey("intializedData")) {
		ERROR_PLATFORM_THROW("Data does not contain required fields for deserialization ");
	}

	_configuration   = fromBase64(encodedState["configuration"].atom);
	assert(_configuration.size() > 0 && _configuration.num_blocks() > 0);
	_invocations     = fromBase64(encodedState["invocations"].atom);
	_history         = fromBase64(encodedState["histories"].atom);
	_initializedData = fromBase64(encodedState["intializedData"].atom);

	for (size_t i = 0; i < USCXML_NUMBER_STATES; i++) {
		if (BIT_HAS(i, _invocations) && USCXML_GET_STATE(i).invoke.size() > 0) {
			for (auto invIter = USCXML_GET_STATE(i).invoke.begin(); invIter != USCXML_GET_STATE(i).invoke.end(); invIter++) {
				try {
					_callbacks->invoke(*invIter);
				} catch (ErrorEvent e) {
					LOG(_callbacks->getLogger(), USCXML_WARN) << e;
				} catch (...) {
				}
			}
		}
	}

	_flags |= USCXML_CTX_INITIALIZED;
}

Data FastMicroStep::serialize() {
	Data encodedState;
	encodedState["configuration"] = Data(toBase64(_configuration));
	encodedState["invocations"] = Data(toBase64(_invocations));
	encodedState["histories"] = Data(toBase64(_history));
	encodedState["intializedData"] = Data(toBase64(_initializedData));
	return encodedState;
}

void FastMicroStep::resortStates(DOMElement* element, const X& xmlPrefix) {

	/**
	 initials
	 deep histories
	 shallow histories
	 everything else
	 */

	// TODO: We can do this in one iteration

	DOMElement* child = element->getFirstElementChild();
	while(child) {
		resortStates(child, xmlPrefix);
		child = child->getNextElementSibling();
	}

	// shallow history states to top
	child = element->getFirstElementChild();
	while(child) {
		if (TAGNAME_CAST(child) == xmlPrefix.str() + "history" &&
		        (!HAS_ATTR(element, kXMLCharType) || iequals(ATTR(element, kXMLCharType), "shallow"))) {

			DOMElement* tmp = child->getNextElementSibling();
			if (child != element->getFirstChild()) {
				element->insertBefore(child, element->getFirstChild());
			}
			child = tmp;
		} else {
			child = child->getNextElementSibling();
		}
	}

	// deep history states to top
	child = element->getFirstElementChild();
	while(child) {
		if (child->getNodeType() == DOMNode::ELEMENT_NODE &&
		        TAGNAME_CAST(child) == xmlPrefix.str() + "history" &&
		        HAS_ATTR(element, kXMLCharType) &&
		        iequals(ATTR(element, kXMLCharType), "deep")) {

			DOMElement* tmp = child->getNextElementSibling();
			if (child != element->getFirstChild()) {
				element->insertBefore(child, element->getFirstChild());
			}
			child = tmp;
		} else {
			child = child->getNextElementSibling();
		}
	}

	// initial states on top of histories even
	child = element->getFirstElementChild();
	while(child) {
		if (child->getNodeType() == DOMNode::ELEMENT_NODE && LOCALNAME_CAST(child) == "initial") {
			DOMElement* tmp = child->getNextElementSibling();
			if (child != element->getFirstChild()) {
				element->insertBefore(child, element->getFirstChild());
			}
			child = tmp;
		} else {
			child = child->getNextElementSibling();
		}
	}
}

std::pair<uint32_t, uint32_t> FastMicroStep::getExitSet(const Transition* transition) {
	if (_exitSetCache.find(transition->postFixOrder) == _exitSetCache.end()) {
		std::pair<uint32_t, uint32_t> statesToExit;
		uint32_t domain = getTransitionDomain(transition);
		if (domain == std::numeric_limits<uint32_t>::max())
			return statesToExit;

		State* domainState = _states[domain];

		// start of exit set
		statesToExit.first = domainState->documentOrder + 1; // do not include domain itself

		// end of exit set
		statesToExit.second = statesToExit.first;

		uint32_t second = statesToExit.first + 1;

		while (second < _states.size()) {
			State *childState = _states[second];

			if (childState->ancestors[domain]) {
				statesToExit.second = second;
			} else {
				break;
			}

			second++;
		}

		_exitSetCache[transition->postFixOrder] = statesToExit;
	}

	return _exitSetCache[transition->postFixOrder];
}
uint32_t FastMicroStep::getTransitionDomain(const Transition* transition) {
	size_t i, j;
	if (!transition->target.any())
		return std::numeric_limits<uint32_t>::max();

	bool internal = (HAS_ATTR(transition->element, kXMLCharType) ? ATTR(transition->element, kXMLCharType) == "internal" : false);
	if (internal && USCXML_STATE_MASK(_states[transition->source]->type) == USCXML_STATE_COMPOUND) {
		i = transition->target.find_first();
		while(i != boost::dynamic_bitset<BITSET_BLOCKTYPE>::npos) {
			if(!(_states[i]->ancestors[transition->source])) {
				goto BREAK_LOOP;
			}
			i = transition->target.find_next(i);

		}
		return _states[transition->source]->documentOrder;
	}
BREAK_LOOP:

	// find LCCA
	uint32_t ancestor = std::numeric_limits<uint32_t>::max();

	// reverse walk up!
	i = _states[transition->source]->parent;
	State* anc = _states[i];

	while(anc) {
		if (USCXML_STATE_MASK(anc->type) != USCXML_STATE_COMPOUND) {
			// LCCA has to be a compound
			anc = _states[anc->parent];
			continue;
		}

		j = transition->target.find_first();
		while(j != boost::dynamic_bitset<BITSET_BLOCKTYPE>::npos) {
			if (!(_states[j]->ancestors[anc->documentOrder])) {
				goto NEXT_ANCESTOR;
			}
			j = transition->target.find_next(j);
		}

		ancestor = anc->documentOrder;
		break;
NEXT_ANCESTOR:
		anc = _states[anc->parent];
		if (anc->documentOrder == 0)
			break;
	}

	// none found - take uppermost root as ancestor
	if (ancestor == std::numeric_limits<uint32_t>::max())
		return 0;
	return ancestor;
}

void FastMicroStep::init(XERCESC_NS::DOMElement* scxml) {

	_scxml = scxml;
	_binding = (HAS_ATTR(_scxml, kXMLCharBinding) && iequals(ATTR(_scxml, kXMLCharBinding), "late") ? LATE : EARLY);
	_xmlPrefix = _scxml->getPrefix();
	_xmlNS = _scxml->getNamespaceURI();
	if (_xmlPrefix) {
		_xmlPrefix = std::string(_xmlPrefix) + ":";
	}

	resortStates(_scxml, _xmlPrefix);

#ifdef WITH_CACHE_FILES
	bool withCache = !envVarIsTrue("USCXML_NOCACHE_FILES");
	Data& cache = _callbacks->getCache().compound["FastMicroStep"];
#endif

	/** -- All things states -- */

	std::list<XERCESC_NS::DOMElement*> tmp;
	size_t i, j;

	tmp = DOMUtils::inDocumentOrder({
		_xmlPrefix.str() + "state",
		_xmlPrefix.str() + "parallel",
		_xmlPrefix.str() + "scxml",
		_xmlPrefix.str() + "initial",
		_xmlPrefix.str() + "final",
		_xmlPrefix.str() + "history"
	}, _scxml);

	_states.resize(tmp.size());
	_configuration.resize(tmp.size());
	_history.resize(tmp.size());
	_initializedData.resize(tmp.size());
	_invocations.resize(tmp.size());

	for (i = 0; i < _states.size(); i++) {
		_states[i] = new State(i);
		_states[i]->element = tmp.front();
		if (HAS_ATTR(_states[i]->element, kXMLCharId)) {
			_states[i]->name = ATTR(_states[i]->element, kXMLCharId);
		}
		_states[i]->element->setUserData(X("uscxmlState"), _states[i], NULL);
		_states[i]->completion.resize(_states.size());
		_states[i]->ancestors.resize(_states.size());
		_states[i]->children.resize(_states.size());
		tmp.pop_front();
	}
	assert(tmp.size() == 0);

	if (_binding == Binding::EARLY && _states.size() > 0) {
		// add all data elements to the first state
		std::list<DOMElement*> dataModels = DOMUtils::filterChildElements(_xmlPrefix.str() + "datamodel", _states[0]->element, true);
		dataModels.erase(std::remove_if(dataModels.begin(),
		                                dataModels.end(),
		[this](DOMElement* elem) {
			return !areFromSameMachine(elem, _scxml);
		}),
		dataModels.end());

		_states[0]->data = DOMUtils::filterChildElements(_xmlPrefix.str() + "data", dataModels, false);
	}

#ifdef WITH_CACHE_FILES
	auto currState = cache.compound["states"].array.begin();
	auto endState = cache.compound["states"].array.end();
#endif

	for (i = 0; i < _states.size(); i++) {
#ifdef WITH_CACHE_FILES
		Data* cachedState = NULL;
		if (withCache) {
			if (currState != endState) {
				cachedState = &(*currState);
				currState++;
			} else {
				cache.compound["states"].array.push_back(Data());
				cachedState = &(*cache.compound["states"].array.rbegin());
			}
		}
#endif
		// collect states with an id attribute
		if (HAS_ATTR(_states[i]->element, kXMLCharId)) {
			_stateIds[ATTR(_states[i]->element, kXMLCharId)] = i;
		}

		// check for executable content and datamodels
		if (_states[i]->element->getChildElementCount() > 0) {
			_states[i]->onEntry = DOMUtils::filterChildElements(_xmlPrefix.str() + "onentry", _states[i]->element);
			_states[i]->onExit = DOMUtils::filterChildElements(_xmlPrefix.str() + "onexit", _states[i]->element);
			_states[i]->invoke = DOMUtils::filterChildElements(_xmlPrefix.str() + "invoke", _states[i]->element);

			if (i == 0) {
				// have global scripts as onentry of <scxml>
				_states[i]->onEntry = DOMUtils::filterChildElements(_xmlPrefix.str() + "script", _states[i]->element, false);
			}

			std::list<DOMElement*> doneDatas = DOMUtils::filterChildElements(_xmlPrefix.str() + "donedata", _states[i]->element);
			if (doneDatas.size() > 0) {
				_states[i]->doneData = doneDatas.front();
			}

			if (_binding == Binding::LATE) {
				std::list<DOMElement*> dataModels = DOMUtils::filterChildElements(_xmlPrefix.str() + "datamodel", _states[i]->element);
				if (dataModels.size() > 0) {
					_states[i]->data = DOMUtils::filterChildElements(_xmlPrefix.str() + "data", dataModels, false);
				}
			}
		}

		// set the states type
		if (false) {
		} else if (iequals(TAGNAME(_states[i]->element), _xmlPrefix.str() + "initial")) {
			_states[i]->type = USCXML_STATE_INITIAL;
		} else if (isFinal(_states[i]->element)) {
			_states[i]->type =  USCXML_STATE_FINAL;
		} else if (isHistory(_states[i]->element)) {
			if (HAS_ATTR(_states[i]->element, kXMLCharType) && iequals(ATTR(_states[i]->element, kXMLCharType), "deep")) {
				_states[i]->type = USCXML_STATE_HISTORY_DEEP;
			} else {
				_states[i]->type = USCXML_STATE_HISTORY_SHALLOW;
			}
		} else if (isAtomic(_states[i]->element)) {
			_states[i]->type = USCXML_STATE_ATOMIC;
		} else if (isParallel(_states[i]->element)) {
			_states[i]->type = USCXML_STATE_PARALLEL;
		} else if (isCompound(_states[i]->element)) {
			_states[i]->type = USCXML_STATE_COMPOUND;
		} else { // <scxml>
			_states[i]->type = USCXML_STATE_COMPOUND;
		}

		// establish the states' completion
#ifdef WITH_CACHE_FILES
		if (withCache && cachedState->compound.find("completion") != cachedState->compound.end()) {
			boost::dynamic_bitset<BITSET_BLOCKTYPE> completion = fromBase64(cachedState->compound["completion"]);
			if (completion.size() != _states.size()) {
				LOG(_callbacks->getLogger(), USCXML_WARN) << "State completion has wrong size: Cache corrupted" << std::endl;
			} else {
				_states[i]->completion = completion;
				goto COMPLETION_STABLISHED;
			}
		}
#endif
		{
			std::list<DOMElement*> completion = getCompletion(_states[i]->element);
			for (j = 0; j < _states.size(); j++) {
				if (!completion.empty() && _states[j]->element == completion.front()) {
					_states[i]->completion[j] = true;
					completion.pop_front();
				} else {
					_states[i]->completion[j] = false;
				}
			}
			assert(completion.size() == 0);
		}
#ifdef WITH_CACHE_FILES
		if (withCache)
			cachedState->compound["completion"] = Data(toBase64(_states[i]->completion));
COMPLETION_STABLISHED:
#endif


#ifdef WITH_CACHE_FILES
		if (withCache && cachedState->compound.find("hasHistoryChild") != cachedState->compound.end()) {
			_states[i]->element->setUserData(X("hasHistoryChild"), _states[strTo<uint32_t>(cachedState->compound["hasHistoryChild"])], NULL);
		}
#endif

		// this is set when establishing the completion
		if (_states[i]->element->getUserData(X("hasHistoryChild")) == _states[i]) {
			_states[i]->type |= USCXML_STATE_HAS_HISTORY;
#ifdef WITH_CACHE_FILES
			if (withCache)
				cachedState->compound["hasHistoryChild"] = Data(((State*)_states[i]->element->getUserData(X("hasHistoryChild")))->documentOrder);
#endif
		}

		// parent relation
		DOMNode* parent = _states[i]->element->getParentNode();
		if (parent && parent->getNodeType() == DOMNode::ELEMENT_NODE) {
			State* uscxmlState = (State*)parent->getUserData(X("uscxmlState"));
			// parent maybe a content element
			if (uscxmlState != NULL) {
				_states[i]->parent = uscxmlState->documentOrder;
			}
		}

		// establish the states' ancestors
		while(parent && parent->getNodeType() == DOMNode::ELEMENT_NODE) {
			State* uscxmlState = (State*)parent->getUserData(X("uscxmlState"));

			if (uscxmlState == NULL)
				break;

			// ancestors
			BIT_SET_AT(uscxmlState->documentOrder, _states[i]->ancestors);

			// children
			BIT_SET_AT(i, uscxmlState->children);
			parent = parent->getParentNode();
		}
	}


	/** -- All things transitions -- */

//	tmp = DOMUtils::inPostFixOrder({_xmlPrefix.str() + "transition"}, _scxml);
	tmp = DOMUtils::inPostFixOrder({
		XML_PREFIX(_scxml).str() + "scxml",
		XML_PREFIX(_scxml).str() + "state",
		XML_PREFIX(_scxml).str() + "final",
		XML_PREFIX(_scxml).str() + "history",
		XML_PREFIX(_scxml).str() + "initial",
		XML_PREFIX(_scxml).str() + "parallel"
	}, _scxml);
	tmp = DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "transition", tmp);

	_transitions.resize(tmp.size());
	_exitSets.resize(tmp.size());

//    std::list<Transition*> transSpontaneous;
//    std::list<Transition*> transEventful;

	for (i = 0; i < _transitions.size(); i++) {
		_transitions[i] = new Transition(i);
		_transitions[i]->element = tmp.front();
		_transitions[i]->conflicts.resize(_transitions.size());
		_transitions[i]->target.resize(_states.size());
		tmp.pop_front();
	}
	assert(tmp.size() == 0);

#ifdef WITH_CACHE_FILES
	auto currTrans = cache.compound["transitions"].array.begin();
	auto endTrans = cache.compound["transitions"].array.end();
#endif

	for (i = 0; i < _transitions.size(); i++) {

#ifdef WITH_CACHE_FILES
		Data* cachedTrans = NULL;
		if (withCache) {
			if (currTrans != endTrans) {
				cachedTrans = &(*currTrans);
				currTrans++;
			} else {
				cache.compound["transitions"].array.push_back(Data());
				cachedTrans = &(*cache.compound["transitions"].array.rbegin());
			}
		}
#endif

		// establish the transitions' target set
#ifdef WITH_CACHE_FILES
		if (withCache && cachedTrans->compound.find("target") != cachedTrans->compound.end()) {
			boost::dynamic_bitset<BITSET_BLOCKTYPE> target = fromBase64(cachedTrans->compound["target"]);
			if (target.size() != _states.size()) {
				LOG(_callbacks->getLogger(), USCXML_WARN) << "Transition target set has wrong size: Cache corrupted" << std::endl;
			} else {
				_transitions[i]->target = target;
				goto TARGET_SET_ESTABLISHED;
			}
		}
#endif
		{
			std::list<std::string> targets = tokenize(ATTR(_transitions[i]->element, kXMLCharTarget));
			for (auto tIter = targets.begin(); tIter != targets.end(); tIter++) {
				if (_stateIds.find(*tIter) != _stateIds.end()) {
					_transitions[i]->target[_stateIds[*tIter]] = true;
				}
			}
		}
#ifdef WITH_CACHE_FILES
		if (withCache)
			cachedTrans->compound["target"] = Data(toBase64(_transitions[i]->target));
TARGET_SET_ESTABLISHED:
#endif
		// the transition's source
		State* uscxmlState = (State*)(_transitions[i]->element->getParentNode()->getUserData(X("uscxmlState")));
		_transitions[i]->source = uscxmlState->documentOrder;


		// the transition's type
		if (!HAS_ATTR(_transitions[i]->element, kXMLCharTarget)) {
			_transitions[i]->type |= USCXML_TRANS_TARGETLESS;
		}

		if (HAS_ATTR(_transitions[i]->element, kXMLCharType) && iequals(ATTR(_transitions[i]->element, kXMLCharType), "internal")) {
			_transitions[i]->type |= USCXML_TRANS_INTERNAL;
		}

		if (!HAS_ATTR(_transitions[i]->element, kXMLCharEvent)) {
			_transitions[i]->type |= USCXML_TRANS_SPONTANEOUS;
//            transSpontaneous.push_back(_transitions[i]);
		} else {
//            transEventful.push_back(_transitions[i]);
		}

		if (iequals(TAGNAME_CAST(_transitions[i]->element->getParentNode()), _xmlPrefix.str() + "history")) {
			_transitions[i]->type |= USCXML_TRANS_HISTORY;
		}

		if (iequals(TAGNAME_CAST(_transitions[i]->element->getParentNode()), _xmlPrefix.str() + "initial")) {
			_transitions[i]->type |= USCXML_TRANS_INITIAL;
		}

		// the transitions event and condition
		_transitions[i]->event = (HAS_ATTR(_transitions[i]->element, kXMLCharEvent) ?
		                          ATTR(_transitions[i]->element, kXMLCharEvent) : "");
		_transitions[i]->cond = (HAS_ATTR(_transitions[i]->element, kXMLCharCond) ?
		                         ATTR(_transitions[i]->element, kXMLCharCond) : "");

		// is there executable content?
		if (_transitions[i]->element->getChildElementCount() > 0) {
			_transitions[i]->onTrans = _transitions[i]->element;
		}

		// establish the transitions' exit set
		assert(_transitions[i]->element != NULL);

		{
			_exitSets[i] = getExitSet(_transitions[i]);
		}
	}

	/**
	 * This bound by cache locality!
	 * Before you change anything, do benchmark!
	 */

#if 0
#define exit1 _exitSets[t1->postFixOrder]
#define exit2 _exitSets[t2->postFixOrder]

	for (size_t set = 0; set < 2; set++) {
		std::list<Transition*>::const_iterator transBegin;
		std::list<Transition*>::const_iterator transEnd;
		if (set == 0) {
			transBegin = transEventful.begin();
			transEnd = transEventful.end();
		} else {
			transBegin = transSpontaneous.begin();
			transEnd = transSpontaneous.end();
		}

		for (auto t1Iter = transBegin; t1Iter != transEnd; t1Iter++) {
			Transition* t1 = *t1Iter;
			auto anc1 = _states[t1->source]->ancestors;
			const uint32_t source1 = t1->source;

			for (auto t2Iter = t1Iter; t2Iter != transEnd; t2Iter++) {
				Transition* t2 = *t2Iter;

				if (exit1.first == 0 && exit2.first == 0) {
					goto COMPATIBLE_TRANS;
				}

				if (exit1.first <= exit2.first && exit1.second >= exit2.first) {
					goto CONFLICTING_TRANS;
				}

				if (exit2.first <= exit1.first && exit2.second >= exit1.first) {
					goto CONFLICTING_TRANS;
				}

COMPATIBLE_TRANS:
				if (t2->source == source1) {
					goto CONFLICTING_TRANS;
				}

				if (anc1[t2->source]) {
					goto CONFLICTING_TRANS;
				}

				if (_states[t2->source]->ancestors[source1]) {
					goto CONFLICTING_TRANS;
				}

				t1->conflicts[t2->postFixOrder] = false;
				//            _transitions[j]->conflicts[i] = false;
				continue;

CONFLICTING_TRANS:
				t1->conflicts[t2->postFixOrder] = true;
				//            _transitions[j]->conflicts[i] = true;

				continue;

			}
		}

		for (auto t1Iter = transBegin; t1Iter != transEnd; t1Iter++) {
			Transition* t1 = *t1Iter;
			// conflicts matrix is symmetric
			for (auto t2Iter = transBegin; t2Iter != t1Iter; t2Iter++) {
				Transition* t2 = *t2Iter;

				t1->conflicts[t2->postFixOrder] = t2->conflicts[t1->postFixOrder];
			}
		}

	}


#else
#define anc1 _states[_transitions[i]->source]->ancestors
#define exit1 _exitSets[i]
#define exit2 _exitSets[j]

	for (i = 0; i < _transitions.size(); i++) {
		anc1 = _states[_transitions[i]->source]->ancestors;
		const uint32_t source1 = _transitions[i]->source;

		for (j = i + 1; j < _transitions.size(); j++) {

			if (exit1.first == 0 && exit2.first == 0) {
				goto COMPATIBLE_TRANS;
			}

			if (exit1.first <= exit2.first && exit1.second >= exit2.first) {
				goto CONFLICTING_TRANS;
			}

			if (exit2.first <= exit1.first && exit2.second >= exit1.first) {
				goto CONFLICTING_TRANS;
			}

COMPATIBLE_TRANS:
			if (_transitions[j]->source == source1) {
				goto CONFLICTING_TRANS;
			}

			if (anc1[_transitions[j]->source]) {
				goto CONFLICTING_TRANS;
			}

			if (_states[_transitions[j]->source]->ancestors[source1]) {
				goto CONFLICTING_TRANS;
			}

			_transitions[i]->conflicts[j] = false;
//            _transitions[j]->conflicts[i] = false;
			continue;
CONFLICTING_TRANS:
			_transitions[i]->conflicts[j] = true;
//            _transitions[j]->conflicts[i] = true;

			continue;

		}
	}

	for (i = 0; i < _transitions.size(); i++) {
		// conflicts matrix is symmetric
		for (j = 0; j < i; j++) {
			_transitions[i]->conflicts[j] = _transitions[j]->conflicts[i];
		}
	}
#endif

	// initialize bitarrays for step()
	_exitSet = boost::dynamic_bitset<BITSET_BLOCKTYPE>(_states.size(), false);
	_entrySet = boost::dynamic_bitset<BITSET_BLOCKTYPE>(_states.size(), false);
	_targetSet = boost::dynamic_bitset<BITSET_BLOCKTYPE>(_states.size(), false);
	_tmpStates = boost::dynamic_bitset<BITSET_BLOCKTYPE>(_states.size(), false);
	_conflicts = boost::dynamic_bitset<BITSET_BLOCKTYPE>(_transitions.size(), false);
	_transSet = boost::dynamic_bitset<BITSET_BLOCKTYPE>(_transitions.size(), false);

	_isInitialized = true;

}

std::string FastMicroStep::toBase64(const boost::dynamic_bitset<BITSET_BLOCKTYPE>& bitset) {
	std::vector<boost::dynamic_bitset<BITSET_BLOCKTYPE>::block_type> bytes(bitset.num_blocks() + 1);
	boost::to_block_range(bitset, bytes.begin());

	std::string encoded;
	encoded.resize(sizeof(boost::dynamic_bitset<BITSET_BLOCKTYPE>::block_type) * bytes.size());
	bytes[bytes.size() - 1] = static_cast<boost::dynamic_bitset<BITSET_BLOCKTYPE>::block_type>(bitset.size());

	static_assert(sizeof(boost::dynamic_bitset<BITSET_BLOCKTYPE>::block_type) >= sizeof(size_t), "Block type too small to encode dynamic_bitset length");

	memcpy(&encoded[0], &bytes[0], sizeof(boost::dynamic_bitset<BITSET_BLOCKTYPE>::block_type) * bytes.size());
	return base64Encode(encoded.c_str(), encoded.size(), true);
}

boost::dynamic_bitset<BITSET_BLOCKTYPE> FastMicroStep::fromBase64(const std::string& encoded) {

	std::string decoded = base64Decode(encoded);
	assert(decoded.size() % sizeof(boost::dynamic_bitset<BITSET_BLOCKTYPE>::block_type) == 0);
	std::vector<boost::dynamic_bitset<BITSET_BLOCKTYPE>::block_type> bytes(decoded.size() / sizeof(boost::dynamic_bitset<BITSET_BLOCKTYPE>::block_type));

	memcpy(&bytes[0], &decoded[0], decoded.size());

	boost::dynamic_bitset<BITSET_BLOCKTYPE> bitset;
	bitset.init_from_block_range(bytes.begin(), --bytes.end());
	bitset.resize(bytes[bytes.size() - 1]);

	return bitset;
}

void FastMicroStep::markAsCancelled() {
	_isCancelled = true;
}

InterpreterState FastMicroStep::step(size_t blockMs) {
	if (!_isInitialized) {
		init(_scxml);
		return USCXML_INITIALIZED;
	}

	std::set<InterpreterMonitor*> monitors = _callbacks->getMonitors();
	size_t i, j, k;

	_exitSet.reset();
	_entrySet.reset();
	_targetSet.reset();
	_tmpStates.reset();

	_conflicts.reset();
	_transSet.reset();

#ifdef USCXML_VERBOSE
	std::cerr << "Config: ";
	printStateNames(_configuration);
#endif

	if (_flags & USCXML_CTX_FINISHED)
		return USCXML_FINISHED;

	if (_flags & USCXML_CTX_TOP_LEVEL_FINAL) {
		USCXML_MONITOR_CALLBACK(monitors, beforeCompletion);

		/* exit all remaining states */
		i = USCXML_NUMBER_STATES;
		while(i-- > 0) {
			if (BIT_HAS(i, _configuration)) {
				/* call all on exit handlers */
				for (auto exitIter = USCXML_GET_STATE(i).onExit.begin(); exitIter != USCXML_GET_STATE(i).onExit.end(); exitIter++) {
					try {
						_callbacks->process(*exitIter);
					} catch (...) {
						// do nothing and continue with next block
					}
				}
				/* Leave configuration intact */
//                BIT_CLEAR(i, _configuration);
			}

			if (BIT_HAS(i, _invocations)) {
				/* cancel all invokers */
				if (USCXML_GET_STATE(i).invoke.size() > 0) {
					for (auto invIter = USCXML_GET_STATE(i).invoke.begin(); invIter != USCXML_GET_STATE(i).invoke.end(); invIter++) {
						_callbacks->uninvoke(*invIter);
					}
				}
				BIT_CLEAR(i, _invocations);
			}
		}

		_flags |= USCXML_CTX_FINISHED;

		USCXML_MONITOR_CALLBACK(monitors, afterCompletion);

		return USCXML_FINISHED;
	}


	if (_flags == USCXML_CTX_PRISTINE) {

		_targetSet |= USCXML_GET_STATE(0).completion;
		_flags |= USCXML_CTX_SPONTANEOUS | USCXML_CTX_INITIALIZED;
		USCXML_MONITOR_CALLBACK(monitors, beforeMicroStep);

		goto ESTABLISH_ENTRYSET;
	}

	if (_flags & USCXML_CTX_SPONTANEOUS) {
		_event = Event();
		goto SELECT_TRANSITIONS;
	}


	if ((_event = _callbacks->dequeueInternal())) {
		USCXML_MONITOR_CALLBACK1(monitors, beforeProcessingEvent, _event);
		goto SELECT_TRANSITIONS;
	}

	/* manage uninvocations */
	i = _invocations.find_first();
	while(i != boost::dynamic_bitset<BITSET_BLOCKTYPE>::npos) {
		/* uninvoke */
		if (!BIT_HAS(i, _configuration) && USCXML_GET_STATE(i).invoke.size() > 0) {
			for (auto invIter = USCXML_GET_STATE(i).invoke.begin(); invIter != USCXML_GET_STATE(i).invoke.end(); invIter++) {
				_callbacks->uninvoke(*invIter);
			}
			BIT_CLEAR(i, _invocations);
		}
		i = _invocations.find_next(i);
	}

	/* manage invocations */
	i = _configuration.find_first();
	while(i != boost::dynamic_bitset<BITSET_BLOCKTYPE>::npos) {
		/* invoke */
		if (!BIT_HAS(i, _invocations) && USCXML_GET_STATE(i).invoke.size() > 0) {
			for (auto invIter = USCXML_GET_STATE(i).invoke.begin(); invIter != USCXML_GET_STATE(i).invoke.end(); invIter++) {
				try {
					_callbacks->invoke(*invIter);
				} catch (ErrorEvent e) {
					LOG(_callbacks->getLogger(), USCXML_WARN) << e;
					// TODO: Shall we deliver the event into the interpreter runtime?
				} catch (...) {
				}
			}
			BIT_SET_AT(i, _invocations)
		}
		i = _configuration.find_next(i);
	}

	// we dequeued all internal events and ought to signal stable configuration
	if (!(_flags & USCXML_CTX_STABLE)) {
		USCXML_MONITOR_CALLBACK(monitors, onStableConfiguration);
		_microstepConfigurations.clear();
		_flags |= USCXML_CTX_STABLE;
		return USCXML_MACROSTEPPED;
	}

	if ((_event = _callbacks->dequeueExternal(blockMs))) {
		USCXML_MONITOR_CALLBACK1(monitors, beforeProcessingEvent, _event);
		goto SELECT_TRANSITIONS;
	}

	if (_isCancelled) {
		// finalize and exit
		_flags |= USCXML_CTX_TOP_LEVEL_FINAL;
		return USCXML_CANCELLED;
	}

//	if (blocking) // we received the empty event to unblock
//        return USCXML_IDLE; // we return IDLE nevertheless

	return USCXML_IDLE;

SELECT_TRANSITIONS:

	// we read an event - unset stable to signal onstable again later
	_flags &= ~USCXML_CTX_STABLE;

	for (i = 0; i < _transitions.size(); i++) {
		/* never select history or initial transitions automatically */
		if unlikely(USCXML_GET_TRANS(i).type & (USCXML_TRANS_HISTORY | USCXML_TRANS_INITIAL))
			continue;

		/* is the transition active? */
		if (BIT_HAS(USCXML_GET_TRANS(i).source, _configuration)) {
			/* is it non-conflicting? */
			if (!BIT_HAS(i, _conflicts)) {
				/* is it spontaneous with an event or vice versa? */
				if ((USCXML_GET_TRANS(i).event.size() == 0 && !_event) ||
				        (USCXML_GET_TRANS(i).event.size() != 0 && _event)) {
					/* is it enabled? */
					if ((!_event || _callbacks->isMatched(_event, USCXML_GET_TRANS(i).event)) &&
					        (USCXML_GET_TRANS(i).cond.size() == 0 || _callbacks->isTrue(USCXML_GET_TRANS(i).cond))) {

						/* remember that we found a transition */
						_flags |= USCXML_CTX_TRANSITION_FOUND;

						/* transitions that are pre-empted */
						_conflicts |= USCXML_GET_TRANS(i).conflicts;

						/* states that are directly targeted (resolve as entry-set later) */
						_targetSet |= USCXML_GET_TRANS(i).target;

						/* states that will be left */
						for (auto documentOrder = _exitSets[i].first;
						        documentOrder <= _exitSets[i].second;
						        documentOrder++) {
							_exitSet[documentOrder] = true;
						}

						BIT_SET_AT(i, _transSet);
					}
				}
			}
		}
	}

#ifdef USCXML_VERBOSE
	std::cerr << "Complete Exit: ";
	printStateNames(exitSet);
#endif

	_exitSet &= _configuration;

	if (_flags & USCXML_CTX_TRANSITION_FOUND) {
		// trigger more sppontaneuous transitions
		_flags |= USCXML_CTX_SPONTANEOUS;
		_flags &= ~USCXML_CTX_TRANSITION_FOUND;
	} else {
		// spontaneuous transitions are exhausted and we will attempt to dequeue an internal event next round
		_flags &= ~USCXML_CTX_SPONTANEOUS;
		return USCXML_MICROSTEPPED;
	}

	USCXML_MONITOR_CALLBACK(monitors, beforeMicroStep);

#ifdef USCXML_VERBOSE
	std::cerr << "Targets: ";
	printStateNames(targetSet);
#endif

#ifdef USCXML_VERBOSE
	std::cerr << "Exiting: ";
	printStateNames(exitSet);
#endif

#ifdef USCXML_VERBOSE
	std::cerr << "History: ";
	printStateNames(_history);
#endif


	/* REMEMBER_HISTORY: */
	for (i = 0; i < _states.size(); i++) {
		if unlikely(USCXML_STATE_MASK(USCXML_GET_STATE(i).type) == USCXML_STATE_HISTORY_SHALLOW ||
		            USCXML_STATE_MASK(USCXML_GET_STATE(i).type) == USCXML_STATE_HISTORY_DEEP) {
			/* a history state whose parent is about to be exited */
			if unlikely(BIT_HAS(USCXML_GET_STATE(i).parent, _exitSet)) {
				_tmpStates = USCXML_GET_STATE(i).completion;

				/* set those states who were enabled */
				_tmpStates &= _configuration;

				/* clear current history with completion mask */
				_history &= ~(USCXML_GET_STATE(i).completion);

				/* set history */
				_history |= _tmpStates;

			}
		}
	}

ESTABLISH_ENTRYSET:
	/* calculate new entry set */
	_entrySet = _targetSet;

	/* iterate for ancestors */
	i = _entrySet.find_first();
	while(i != boost::dynamic_bitset<BITSET_BLOCKTYPE>::npos) {
		_entrySet |= USCXML_GET_STATE(i).ancestors;
		i = _entrySet.find_next(i);
	}

	/* iterate for descendants */
	i = _entrySet.find_first();
	while(i != boost::dynamic_bitset<BITSET_BLOCKTYPE>::npos) {

		switch (USCXML_STATE_MASK(USCXML_GET_STATE(i).type)) {
		case USCXML_STATE_FINAL:
		case USCXML_STATE_ATOMIC:
			break;

		case USCXML_STATE_PARALLEL: {
			_entrySet |= USCXML_GET_STATE(i).completion;
			break;
		}

		case USCXML_STATE_HISTORY_SHALLOW:
		case USCXML_STATE_HISTORY_DEEP: {
			if (!BIT_HAS_AND(USCXML_GET_STATE(i).completion, _history) &&
			        !BIT_HAS(USCXML_GET_STATE(i).parent, _configuration)) {

				/* nothing set for history, look for a default transition */
				for (j = 0; j < _transitions.size(); j++) {
					if unlikely(USCXML_GET_TRANS(j).source == i) {
						_entrySet |= USCXML_GET_TRANS(j).target;

						if(USCXML_STATE_MASK(USCXML_GET_STATE(i).type) == USCXML_STATE_HISTORY_DEEP &&
						        !BIT_HAS_AND(USCXML_GET_TRANS(j).target, USCXML_GET_STATE(i).children)) {
							for (k = i + 1; k < _states.size(); k++) {
								if (BIT_HAS(k, USCXML_GET_TRANS(j).target)) {
									_entrySet |= USCXML_GET_STATE(k).ancestors;
									break;
								}
							}
						}
						BIT_SET_AT(j, _transSet);
						break;
					}
					/* Note: SCXML mandates every history to have a transition! */
				}
			} else {
				_tmpStates = USCXML_GET_STATE(i).completion;
				_tmpStates &= _history;
				_entrySet |= _tmpStates;

				if (USCXML_GET_STATE(i).type == (USCXML_STATE_HAS_HISTORY | USCXML_STATE_HISTORY_DEEP)) {
					/* a deep history state with nested histories -> more completion */
					for (j = i + 1; j < USCXML_NUMBER_STATES; j++) {
						if (BIT_HAS(j, USCXML_GET_STATE(i).completion) &&
						        BIT_HAS(j, _entrySet) &&
						        (USCXML_GET_STATE(j).type & USCXML_STATE_HAS_HISTORY)) {
							for (k = j + 1; k < USCXML_NUMBER_STATES; k++) {
								/* add nested history to entry_set */
								if ((USCXML_STATE_MASK(USCXML_GET_STATE(k).type) == USCXML_STATE_HISTORY_DEEP ||
								        USCXML_STATE_MASK(USCXML_GET_STATE(k).type) == USCXML_STATE_HISTORY_SHALLOW) &&
								        BIT_HAS(k, USCXML_GET_STATE(j).children)) {
									/* a nested history state */
									BIT_SET_AT(k, _entrySet);
								}
							}
						}
					}
				}
			}
			break;
		}

		case USCXML_STATE_INITIAL: {
			for (j = 0; j < USCXML_NUMBER_TRANS; j++) {
				if (USCXML_GET_TRANS(j).source == i) {
					BIT_SET_AT(j, _transSet);
					BIT_CLEAR(i, _entrySet);
					_entrySet |= USCXML_GET_TRANS(j).target;
					for (k = i + 1; k < USCXML_NUMBER_STATES; k++) {
						if (BIT_HAS(k, USCXML_GET_TRANS(j).target)) {
							_entrySet |= USCXML_GET_STATE(k).ancestors;
						}
					}
				}
			}
			break;
		}
		case USCXML_STATE_COMPOUND: { /* we need to check whether one child is already in entry_set */
			if (!BIT_HAS_AND(_entrySet, USCXML_GET_STATE(i).children) &&
			        (!BIT_HAS_AND(_configuration, USCXML_GET_STATE(i).children) ||
			         BIT_HAS_AND(_exitSet, USCXML_GET_STATE(i).children))) {
				_entrySet |= USCXML_GET_STATE(i).completion;
				if (!BIT_HAS_AND(USCXML_GET_STATE(i).completion, USCXML_GET_STATE(i).children)) {
					/* deep completion */
					for (j = i + 1; j < USCXML_NUMBER_STATES; j++) {
						if (BIT_HAS(j, USCXML_GET_STATE(i).completion)) {
							_entrySet |= USCXML_GET_STATE(j).ancestors;
							break; /* completion of compound is single state */
						}
					}
				}
			}
			break;
		}
		}
		i = _entrySet.find_next(i);

	}


#ifdef USCXML_VERBOSE
	std::cerr << "Transitions: " << transSet << std::endl;
#endif

	/* EXIT_STATES: */
	/* we cannot use find_first due to ordering */
	i = USCXML_NUMBER_STATES;
	while(i-- > 0) {
		if (BIT_HAS(i, _exitSet) && BIT_HAS(i, _configuration)) {

			USCXML_MONITOR_CALLBACK2(monitors, beforeExitingState, USCXML_GET_STATE(i).name, USCXML_GET_STATE(i).element);

			/* call all on exit handlers */
			for (auto exitIter = USCXML_GET_STATE(i).onExit.begin(); exitIter != USCXML_GET_STATE(i).onExit.end(); exitIter++) {
				try {
					_callbacks->process(*exitIter);
				} catch (...) {
					// do nothing and continue with next block
				}
			}
			BIT_CLEAR(i, _configuration);

			USCXML_MONITOR_CALLBACK2(monitors, afterExitingState, USCXML_GET_STATE(i).name, USCXML_GET_STATE(i).element);

		}
	}

	/* TAKE_TRANSITIONS: */
	i = _transSet.find_first();
	while(i != boost::dynamic_bitset<BITSET_BLOCKTYPE>::npos) {
		if ((USCXML_GET_TRANS(i).type & (USCXML_TRANS_HISTORY | USCXML_TRANS_INITIAL)) == 0) {
			USCXML_MONITOR_CALLBACK1(monitors, beforeTakingTransition, USCXML_GET_TRANS(i).element);

			if (USCXML_GET_TRANS(i).onTrans != NULL) {

				/* call executable content in non-history, non-initial transition */
				try {
					_callbacks->process(USCXML_GET_TRANS(i).onTrans);
				} catch (...) {
					// do nothing and continue with next block
				}
			}

			USCXML_MONITOR_CALLBACK1(monitors, afterTakingTransition, USCXML_GET_TRANS(i).element);

		}
		i = _transSet.find_next(i);
	}

#ifdef USCXML_VERBOSE
	std::cerr << "Entering: ";
	printStateNames(entrySet);
#endif


	/* ENTER_STATES: */
	i = _entrySet.find_first();
	while(i != boost::dynamic_bitset<BITSET_BLOCKTYPE>::npos) {

		if (BIT_HAS(i, _configuration)) {
			// already active
			i = _entrySet.find_next(i);
			continue;
		}

		/* these are no proper states */
		if unlikely(USCXML_STATE_MASK(USCXML_GET_STATE(i).type) == USCXML_STATE_HISTORY_DEEP ||
		            USCXML_STATE_MASK(USCXML_GET_STATE(i).type) == USCXML_STATE_HISTORY_SHALLOW ||
		            USCXML_STATE_MASK(USCXML_GET_STATE(i).type) == USCXML_STATE_INITIAL) {
			i = _entrySet.find_next(i);
			continue;
		}

		USCXML_MONITOR_CALLBACK2(monitors, beforeEnteringState, USCXML_GET_STATE(i).name, USCXML_GET_STATE(i).element);

		BIT_SET_AT(i, _configuration);

		/* initialize data */
		if (!BIT_HAS(i, _initializedData)) {
			for (auto dataIter = USCXML_GET_STATE(i).data.begin(); dataIter != USCXML_GET_STATE(i).data.end(); dataIter++) {
				_callbacks->initData(*dataIter);
			}
			BIT_SET_AT(i, _initializedData);
		}

		/* call all on entry handlers */
		for (auto entryIter = USCXML_GET_STATE(i).onEntry.begin(); entryIter != USCXML_GET_STATE(i).onEntry.end(); entryIter++) {
			try {
				_callbacks->process(*entryIter);
			} catch (...) {
				// do nothing and continue with next block
			}
		}

		USCXML_MONITOR_CALLBACK2(monitors, afterEnteringState, USCXML_GET_STATE(i).name, USCXML_GET_STATE(i).element);

		/* take history and initial transitions */
		j = _transSet.find_first();
		while(j != boost::dynamic_bitset<BITSET_BLOCKTYPE>::npos) {
			if unlikely((USCXML_GET_TRANS(j).type & (USCXML_TRANS_HISTORY | USCXML_TRANS_INITIAL)) &&
			            USCXML_GET_STATE(USCXML_GET_TRANS(j).source).parent == i) {

				USCXML_MONITOR_CALLBACK1(monitors, beforeTakingTransition, USCXML_GET_TRANS(j).element);

				/* call executable content in transition */
				if (USCXML_GET_TRANS(j).onTrans != NULL) {
					try {
						_callbacks->process(USCXML_GET_TRANS(j).onTrans);
					} catch (...) {
						// do nothing and continue with next block
					}
				}

				USCXML_MONITOR_CALLBACK1(monitors, afterTakingTransition, USCXML_GET_TRANS(j).element);
			}

			j = _transSet.find_next(j);
		}

		/* handle final states */
		if unlikely(USCXML_STATE_MASK(USCXML_GET_STATE(i).type) == USCXML_STATE_FINAL) {
			if unlikely(USCXML_GET_STATE(i).ancestors.count() == 1 && BIT_HAS(0, USCXML_GET_STATE(i).ancestors)) {
				// only the topmost scxml is an ancestor
				_flags |= USCXML_CTX_TOP_LEVEL_FINAL;
			} else {
				/* raise done event */
				_callbacks->raiseDoneEvent(USCXML_GET_STATE(USCXML_GET_STATE(i).parent).element, USCXML_GET_STATE(i).doneData);
			}

			/**
			 * are we the last final state to leave a parallel state?:
			 * 1. Gather all parallel states in our ancestor chain
			 * 2. Find all states for which these parallels are ancestors
			 * 3. Iterate all active final states and remove their ancestors
			 * 4. If a state remains, not all children of a parallel are final
			 */
			j = USCXML_GET_STATE(i).ancestors.find_first();
			while(j != boost::dynamic_bitset<BITSET_BLOCKTYPE>::npos) {
				if unlikely(USCXML_STATE_MASK(USCXML_GET_STATE(j).type) == USCXML_STATE_PARALLEL) {
					_tmpStates.reset();
					k = _configuration.find_first();
					while (k != boost::dynamic_bitset<BITSET_BLOCKTYPE>::npos) {
						if (BIT_HAS(j, USCXML_GET_STATE(k).ancestors)) {
							if (USCXML_STATE_MASK(USCXML_GET_STATE(k).type) == USCXML_STATE_FINAL) {
								_tmpStates ^= USCXML_GET_STATE(k).ancestors;
							} else {
								BIT_SET_AT(k, _tmpStates);
							}
						}
						k = _configuration.find_next(k);
					}
					if (!_tmpStates.any()) {
						// raise done for state j
						_callbacks->raiseDoneEvent(USCXML_GET_STATE(j).element, USCXML_GET_STATE(j).doneData);
					}
				}

				j = USCXML_GET_STATE(i).ancestors.find_next(j);
			}
		}
	}
	USCXML_MONITOR_CALLBACK(monitors, afterMicroStep);

	// are we running in circles?
	if (_microstepConfigurations.find(_configuration) != _microstepConfigurations.end()) {
		InterpreterIssue issue("Reentering same configuration during microstep  - possible endless loop",
		                       NULL,
		                       InterpreterIssue::USCXML_ISSUE_WARNING);

		USCXML_MONITOR_CALLBACK1(monitors,
		                         reportIssue,
		                         issue);
	}
	_microstepConfigurations.insert(_configuration);

	return USCXML_MICROSTEPPED;
}

void FastMicroStep::reset() {
	_isCancelled = false;
	_flags = USCXML_CTX_PRISTINE;
	_configuration.reset();
	_history.reset();
	_initializedData.reset();
	_invocations.reset();

}

bool FastMicroStep::isInState(const std::string& stateId) {
#ifdef USCXML_VERBOSE
	printStateNames(_configuration);
#endif
	if (_stateIds.find(stateId) == _stateIds.end())
		return false;
	return _configuration[_stateIds[stateId]];
}

std::list<XERCESC_NS::DOMElement*> FastMicroStep::getConfiguration() {
	std::list<XERCESC_NS::DOMElement*> config;
	size_t i = _configuration.find_first();
	while(i != boost::dynamic_bitset<BITSET_BLOCKTYPE>::npos) {
		config.push_back(_states[i]->element);
		i = _configuration.find_next(i);
	}
	return config;
}


std::list<DOMElement*> FastMicroStep::getHistoryCompletion(const DOMElement* history) {
	std::set<std::string> elements;
	elements.insert(_xmlPrefix.str() + "history");
	std::list<DOMElement*> histories = DOMUtils::inPostFixOrder(elements, _scxml);

	std::list<DOMElement*> covered;
	std::list<DOMElement*> perParentcovered;
	const DOMNode* parent = NULL;

	std::list<DOMElement*> completion;


	if (parent != history->getParentNode()) {
		covered.insert(covered.end(), perParentcovered.begin(), perParentcovered.end());
		perParentcovered.clear();
		parent = history->getParentNode();
	}

	bool deep = (HAS_ATTR(history, kXMLCharType) && iequals(ATTR(history, kXMLCharType), "deep"));

	for (size_t j = 0; j < _states.size(); j++) {
		if (_states[j]->element == history)
			continue;

		if (DOMUtils::isDescendant((DOMNode*)_states[j]->element, history->getParentNode()) && isHistory(_states[j]->element)) {
			((DOMElement*)history)->setUserData(X("hasHistoryChild"), _states[j], NULL);
		}

		if (DOMUtils::isMember(_states[j]->element, covered))
			continue;

		if (deep) {
			if (DOMUtils::isDescendant(_states[j]->element, history->getParentNode()) && !isHistory(_states[j]->element)) {
				completion.push_back(_states[j]->element);
			}
		} else {
			if (_states[j]->element->getParentNode() == history->getParentNode() && !isHistory(_states[j]->element)) {
				completion.push_back(_states[j]->element);
			}
		}
	}

	return completion;
}

#ifdef USCXML_VERBOSE
/**
 * Print name of states contained in a (debugging).
 */
void FastMicroStep::printStateNames(const boost::dynamic_bitset<BITSET_BLOCKTYPE>& a) {
	size_t i;
	const char* seperator = "";
	for (i = 0; i < a.size(); i++) {
		if (BIT_HAS(i, a)) {
			std::cerr << seperator << (HAS_ATTR(USCXML_GET_STATE(i).element, X("id")) ? ATTR(USCXML_GET_STATE(i).element, X("id")) : "UNK");
			seperator = ", ";
		}
	}
	std::cerr << std::endl;
}
#endif

std::list<DOMElement*> FastMicroStep::getCompletion(const DOMElement* state) {

	if (isHistory(state)) {
		// we already did in setHistoryCompletion
		return getHistoryCompletion(state);

	} else if (isParallel(state)) {
		return getChildStates(state);

	} else if (HAS_ATTR(state, kXMLCharInitial)) {
		return getStates(tokenize(ATTR(state, kXMLCharInitial)), _scxml);

	} else {
		std::list<DOMElement*> completion;

		std::list<DOMElement*> initElems = DOMUtils::filterChildElements(_xmlPrefix.str() + "initial", state);
		if(initElems.size() > 0) {
			// initial element is first child
			completion.push_back(initElems.front());
		} else {
			// first child state
			for (auto childElem = state->getFirstElementChild(); childElem; childElem = childElem->getNextElementSibling()) {
				if (isState(childElem)) {
					completion.push_back(childElem);
					break;
				}
			}
		}
		return completion;
	}

}


#if 0
/**
 * See: http://www.w3.org/TR/scxml/#LegalStateConfigurations
 */
bool FastMicroStep::hasLegalConfiguration() {

	// The configuration contains exactly one child of the <scxml> element.
	std::list<DOMElement*> scxmlChilds = getChildStates(_scxml, true);
	DOMNode* foundScxmlChild;
	for (auto sIter = scxmlChilds.begin(); sIter != scxmlChilds.end(); sIter++) {
		DOMElement* state = *sIter;
		if (isMember(state, config)) {
			if (foundScxmlChild) {
				LOG(USCXML_ERROR) << "Invalid configuration: Multiple childs of scxml root are active '" << ATTR_CAST(foundScxmlChild, "id") << "' and '" << ATTR_CAST(scxmlChilds[i], "id") << "'" << std::endl;
				return false;
			}
			foundScxmlChild = scxmlChilds[i];
		}
	}
	if (!foundScxmlChild) {
		LOG(USCXML_ERROR) << "Invalid configuration: No childs of scxml root are active" << std::endl;

		return false;
	}

	// The configuration contains one or more atomic states.
	bool foundAtomicState = false;
	for (size_t i = 0; i < config.size(); i++) {
		if (isAtomic(Element<std::string>(config[i]))) {
			foundAtomicState = true;
			break;
		}
	}
	if (!foundAtomicState) {
		LOG(USCXML_ERROR) << "Invalid configuration: No atomic state is active" << std::endl;
		return false;
	}

	// the configuration contains no history pseudo-states
	for (size_t i = 0; i < config.size(); i++) {
		if (isHistory(Element<std::string>(config[i]))) {
			LOG(USCXML_ERROR) << "Invalid configuration: history state " << ATTR_CAST(config[i], "id") << " is active" << std::endl;
			return false;
		}
	}

	// When the configuration contains an atomic state, it contains all of its <state> and <parallel> ancestors.
	for (size_t i = 0; i < config.size(); i++) {
		if (isAtomic(Element<std::string>(config[i]))) {
			Node<std::string> parent = config[i];
			while(((parent = parent.getParentNode()) && parent.getNodeType() == Node_base::ELEMENT_NODE)) {
				if (isState(Element<std::string>(parent)) &&
				        (iequals(LOCALNAME(parent), "state") ||
				         iequals(LOCALNAME(parent), "parallel"))) {
					if (!isMember(parent, config)) {
						LOG(USCXML_ERROR) << "Invalid configuration: atomic state '" << ATTR_CAST(config[i], "id") << "' is active, but parent '" << ATTR_CAST(parent, "id") << "' is not" << std::endl;
						return false;
					}
				}
			}
		}
	}

	// When the configuration contains a non-atomic <state>, it contains one and only one of the state's children
	for (size_t i = 0; i < config.size(); i++) {
		Element<std::string> configElem(config[i]);
		if (!isAtomic(configElem) && !isParallel(configElem)) {
			Node<std::string> foundChildState;
			//std::cerr << config[i] << std::endl;
			NodeSet<std::string> childs = getChildStates(config[i]);
			for (size_t j = 0; j < childs.size(); j++) {
				//std::cerr << childs[j] << std::endl;
				if (isMember(childs[j], config)) {
					if (foundChildState) {
						LOG(USCXML_ERROR) << "Invalid configuration: Multiple childs of compound '" << ATTR_CAST(config[i], "id")
						                  << "' are active '" << ATTR_CAST(foundChildState, "id") << "' and '" << ATTR_CAST(childs[j], "id") << "'" << std::endl;
						return false;
					}
					foundChildState = childs[j];
				}
			}
			if (!foundChildState) {
				LOG(USCXML_ERROR) << "Invalid configuration: No childs of compound '" << ATTR_CAST(config[i], "id") << "' are active" << std::endl;
				return false;
			}
		}
	}

	// If the configuration contains a <parallel> state, it contains all of its children
	for (size_t i = 0; i < config.size(); i++) {
		if (isParallel(Element<std::string>(config[i]))) {
			NodeSet<std::string> childs = getChildStates(config[i]);
			for (size_t j = 0; j < childs.size(); j++) {
				if (!isMember(childs[j], config) && !isHistory(Element<std::string>(childs[j]))) {
					LOG(USCXML_ERROR) << "Invalid configuration: Not all children of parallel '" << ATTR_CAST(config[i], "id") << "' are active i.e. '" << ATTR_CAST(childs[j], "id") << "' is not" << std::endl;
					return false;
				}
			}
		}
	}

	// everything worked out fine!
	return true;
}
#endif

}
