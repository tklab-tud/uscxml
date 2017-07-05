/**
 *  @file
 *  @author     2017 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#include "LargeMicroStep.h"
#include "uscxml/debug/Benchmark.h"
#include "uscxml/util/Predicates.h"

#include <algorithm>
#include <iostream>

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

#ifdef __GNUC__
#  define likely(x)       (__builtin_expect(!!(x), 1))
#  define unlikely(x)     (__builtin_expect(!!(x), 0))
#else
#  define likely(x)       (x)
#  define unlikely(x)     (x)
#endif

#if 0
#define BENCHMARK(domain) Benchmark bench(domain);
#else
#define BENCHMARK(domain)
#endif

#ifdef USCXML_VERBOSE
#include <iostream>
#endif
namespace uscxml {

using namespace XERCESC_NS;

#ifdef USCXML_VERBOSE
/**
 * Print name of states contained in a (debugging).
 */
void LargeMicroStep::printStateNames(const boost::container::flat_set<LargeMicroStep::State*, LargeMicroStep::StateOrder>& a) {
	const char* seperator = "";
	for (auto state : a) {
		std::cerr << seperator << (HAS_ATTR(state->element, X("id")) ? ATTR(state->element, X("id")) : "UNK");
		seperator = ", ";
	}
	std::cerr << std::endl;
}
#endif

LargeMicroStep::LargeMicroStep(MicroStepCallbacks* callbacks) : MicroStepImpl(callbacks) {
}

std::shared_ptr<MicroStepImpl> LargeMicroStep::create(MicroStepCallbacks* callbacks) {
	return std::shared_ptr<MicroStepImpl>(new LargeMicroStep(callbacks));
}

LargeMicroStep::~LargeMicroStep() {
	for (size_t i = 0; i < _states.size(); i++) {
		delete(_states[i]);
	}
	for (size_t i = 0; i < _transitions.size(); i++) {
		delete(_transitions[i]);
	}
}

std::list<XERCESC_NS::DOMElement*> LargeMicroStep::getConfiguration() {
	std::list<XERCESC_NS::DOMElement*> config;
	for (auto state : _configuration) {
		config.push_back(state->element);
	}
	return config;
}

void LargeMicroStep::markAsCancelled() {
	_isCancelled = true;
}

void LargeMicroStep::reset() {
	_isCancelled = false;
	_flags = USCXML_CTX_PRISTINE;
	_configuration.clear();
	_configurationPostFix.clear();
	_history.clear();
	_initializedData.clear();
	_invocations.clear();

}

bool LargeMicroStep::isInState(const std::string& stateId) {
#ifdef USCXML_VERBOSE
	printStateNames(_configuration);
#endif
	for (auto state : _configuration) {
		if (HAS_ATTR(state->element, kXMLCharId) && ATTR(state->element, kXMLCharId) == stateId)
			return true;
	}
	return false;
}

std::list<DOMElement*> LargeMicroStep::getHistoryCompletion(const DOMElement* history) {
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

std::list<DOMElement*> LargeMicroStep::getCompletion(const DOMElement* state) {
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

void LargeMicroStep::init(XERCESC_NS::DOMElement* scxml) {
	_scxml = scxml;
	_binding = (HAS_ATTR(_scxml, kXMLCharBinding) && iequals(ATTR(_scxml, kXMLCharBinding), "late") ? LATE : EARLY);
	_xmlPrefix = _scxml->getPrefix();
	_xmlNS = _scxml->getNamespaceURI();
	if (_xmlPrefix) {
		_xmlPrefix = std::string(_xmlPrefix) + ":";
	}

	{
		BENCHMARK("init resort states")
		resortStates(_scxml, _xmlPrefix);
	}

	std::set<std::string> stateIds;

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

	for (i = 0; i < _states.size(); i++) {
		_states[i] = new State(i);
		_states[i]->element = tmp.front();
		if (HAS_ATTR(_states[i]->element, kXMLCharId)) {
			_states[i]->name = ATTR(_states[i]->element, kXMLCharId);
		}
		_states[i]->element->setUserData(X("uscxmlState"), _states[i], NULL);
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

		std::list<XERCESC_NS::DOMElement*> dataList = DOMUtils::filterChildElements(_xmlPrefix.str() + "data", dataModels, false);
		_states[0]->data = { std::make_move_iterator(std::begin(dataList)), std::make_move_iterator(std::end(dataList))};
	}

	for (i = 0; i < _states.size(); i++) {
		// collect states with an id attribute
		if (HAS_ATTR(_states[i]->element, kXMLCharId)) {
			stateIds.insert(ATTR(_states[i]->element, kXMLCharId));
		}

		// TODO: Reserve space for ancestors? => Measure performance!

		// check for executable content and datamodels
		if (_states[i]->element->getChildElementCount() > 0) {
			// not every child element will be a child state, but we can shrink later
			_states[i]->children.reserve(_states[i]->element->getChildElementCount());

			std::list<XERCESC_NS::DOMElement*> entryList = DOMUtils::filterChildElements(_xmlPrefix.str() + "onentry", _states[i]->element);
			std::list<XERCESC_NS::DOMElement*> exitList = DOMUtils::filterChildElements(_xmlPrefix.str() + "onexit", _states[i]->element);
			std::list<XERCESC_NS::DOMElement*> invokeList = DOMUtils::filterChildElements(_xmlPrefix.str() + "invoke", _states[i]->element);
			_states[i]->onEntry = { std::make_move_iterator(std::begin(entryList)), std::make_move_iterator(std::end(entryList))};
			_states[i]->onExit = { std::make_move_iterator(std::begin(exitList)), std::make_move_iterator(std::end(exitList))};
			_states[i]->invoke = { std::make_move_iterator(std::begin(invokeList)), std::make_move_iterator(std::end(invokeList))};

			if (i == 0) {
				// have global scripts as onentry of <scxml>
				std::list<XERCESC_NS::DOMElement*> scriptList = DOMUtils::filterChildElements(_xmlPrefix.str() + "script", _states[i]->element, false);
				_states[i]->onEntry = { std::make_move_iterator(std::begin(scriptList)), std::make_move_iterator(std::end(scriptList))};
			}

			std::list<DOMElement*> doneDatas = DOMUtils::filterChildElements(_xmlPrefix.str() + "donedata", _states[i]->element);
			if (doneDatas.size() > 0) {
				_states[i]->doneData = doneDatas.front();
			}

			if (_binding == Binding::LATE) {
				std::list<DOMElement*> dataModels = DOMUtils::filterChildElements(_xmlPrefix.str() + "datamodel", _states[i]->element);
				if (dataModels.size() > 0) {
					std::list<XERCESC_NS::DOMElement*> dataList = DOMUtils::filterChildElements(_xmlPrefix.str() + "data", dataModels, false);
					_states[i]->data = { std::make_move_iterator(std::begin(dataList)), std::make_move_iterator(std::end(dataList))};
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
		} else { // <scxml> and any other state
			_states[i]->type = USCXML_STATE_COMPOUND;
		}

		// establish the states' completion
		std::list<DOMElement*> completionList = getCompletion(_states[i]->element);
		for (j = 0; completionList.size() > 0; j++) {
			_states[i]->completion.insert((State*)completionList.front()->getUserData(X("uscxmlState")));
			completionList.pop_front();
		}
		assert(completionList.size() == 0);

		// this is set when establishing the completion
		if (_states[i]->element->getUserData(X("hasHistoryChild")) == _states[i]) {
			_states[i]->type |= USCXML_STATE_HAS_HISTORY;
		}

		// set the states parent and add us as a children
		DOMNode* parent = _states[i]->element->getParentNode();
		if (parent && parent->getNodeType() == DOMNode::ELEMENT_NODE) {
			_states[i]->parent = (State*)parent->getUserData(X("uscxmlState"));
			if (_states[i]->parent != NULL) {
				_states[i]->parent->children.push_back(_states[i]);
				_states[i]->ancestors.insert(_states[i]->parent);
				_states[i]->ancestors.insert(_states[i]->parent->ancestors.begin(), _states[i]->parent->ancestors.end());
			}
		}
	}

	/** -- All things transitions -- */

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
	_conflicting.resize(tmp.size());
	_compatible.resize(tmp.size());

	for (i = 0; i < _transitions.size(); i++) {
		_transitions[i] = new Transition(i);
		_transitions[i]->element = tmp.front();
		_transitions[i]->element->setUserData(X("uscxmlTrans"), _transitions[i], NULL);
		tmp.pop_front();
	}
	assert(tmp.size() == 0);


	for (i = 0; i < _transitions.size(); i++) {
		// establish the transitions' target set
		{
			std::list<std::string> targets = tokenize(ATTR(_transitions[i]->element, kXMLCharTarget));
			_transitions[i]->target.reserve(targets.size());

			for (auto tIter = targets.begin(); tIter != targets.end(); tIter++) {
				if (stateIds.find(*tIter) != stateIds.end()) {
					_transitions[i]->target.push_back((State*)getState(*tIter, _scxml)->getUserData(X("uscxmlState")));
				}
			}
		}

		// the transition's type
		if (!HAS_ATTR(_transitions[i]->element, kXMLCharTarget)) {
			_transitions[i]->type |= USCXML_TRANS_TARGETLESS;
		}

		if (HAS_ATTR(_transitions[i]->element, kXMLCharType) && iequals(ATTR(_transitions[i]->element, kXMLCharType), "internal")) {
			_transitions[i]->type |= USCXML_TRANS_INTERNAL;
		}

		if (!HAS_ATTR(_transitions[i]->element, kXMLCharEvent)) {
			_transitions[i]->type |= USCXML_TRANS_SPONTANEOUS;
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

	}

	/* Connect states and transitions */
	for (auto state : _states) {
		std::list<XERCESC_NS::DOMElement*> transList = DOMUtils::filterChildElements(_xmlPrefix.str() + "transition", state->element);
		if (transList.size() > 0) {
			state->transitions.resize(transList.size());
			for (auto i = 0; transList.size() > 0; i++) {
				auto trans = transList.front();
				transList.pop_front();
				Transition* uscxmlTrans = ((Transition*)trans->getUserData(X("uscxmlTrans")));
				uscxmlTrans->source = state;
				// save some memory? => Measure performance!
//                uscxmlTrans->compatible.shrink_to_fit();
//                uscxmlTrans->exitSet.shrink_to_fit();

				state->transitions[i] = uscxmlTrans;
			}
			// we need the postfix order for iterating transitions of active states
			state->postFixOrder = (*(state->transitions.begin()))->postFixOrder;
		} else {
			state->postFixOrder = std::numeric_limits<uint32_t>::max();
		}

		// save some memory? => Measure performance!
//        state->ancestors.shrink_to_fit();
		state->children.shrink_to_fit();
//        state->completion.shrink_to_fit();

		assert(transList.size() == 0);
	}

	_isInitialized = true;
}

InterpreterState LargeMicroStep::step(size_t blockMs) {
	if (!_isInitialized) {
		init(_scxml);
		return USCXML_INITIALIZED;
	}

	std::set<InterpreterMonitor*> monitors = _callbacks->getMonitors();

	_exitSet.clear();
	_entrySet.clear();
	_targetSet.clear();
	_tmpStates.clear();

	_compatible.clear();
	_conflicting.clear();
	_transSet.clear();

	if (_flags & USCXML_CTX_FINISHED)
		return USCXML_FINISHED;

	if (_flags & USCXML_CTX_TOP_LEVEL_FINAL) {
		USCXML_MONITOR_CALLBACK(monitors, beforeCompletion);

		/* exit all remaining states */
		for (auto stateIter = _configuration.end() ; stateIter != _configuration.begin() ; /* Do nothing */ ) {
			--stateIter;
			/* call all on exit handlers */
			for (auto onExit : (*stateIter)->onExit) {
				try {
					_callbacks->process(onExit);
				} catch (...) {
					// do nothing and continue with next block
				}
			}
			if (_invocations.find(*stateIter) != _invocations.end()) {
				/* cancel all invokers */
				for (auto invoke : (*stateIter)->invoke) {
					_callbacks->uninvoke(invoke);
				}
				_invocations.clear();
			}
		}

		_flags |= USCXML_CTX_FINISHED;

		USCXML_MONITOR_CALLBACK(monitors, afterCompletion);

		return USCXML_FINISHED;
	}


	if (_flags == USCXML_CTX_PRISTINE) {
		// TODO: Is this working?
		_targetSet = _states.front()->completion;
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
	for (auto invokeIter = _invocations.begin(); invokeIter != _invocations.end();) {
		if (_configuration.find(*invokeIter) == _configuration.end()) {
			/* uninvoke */
			for (auto invoke : (*invokeIter)->invoke) {
				_callbacks->uninvoke(invoke);
			}
			invokeIter = _invocations.erase(invokeIter);
		} else {
			invokeIter++;
		}
	}

	/* manage invocations */
	for (auto config : _configuration) {
		if (_invocations.find(config) == _invocations.end()) {
			for (auto invoke : config->invoke) {
				try {
					/* invoke */
					_callbacks->invoke(invoke);
				} catch (ErrorEvent e) {
					LOG(_callbacks->getLogger(), USCXML_WARN) << e;
					// TODO: Shall we deliver the event into the interpreter runtime?
				} catch (...) {
				}
			}
		}
		_invocations.insert(config);
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

	{
		BENCHMARK("select transitions");

		// iterate active states in postfix order and find transitions
		for (auto stateIter = _configurationPostFix.begin(); stateIter != _configurationPostFix.end();) {
			State* state = *stateIter++;
//            std::cout << (HAS_ATTR(state->element, kXMLCharId) ? ATTR(state->element, kXMLCharId) : "?");
//            std::cout << ": " << state->documentOrder << " - " << state->postFixOrder << std::endl;

			for (auto transIter = state->transitions.begin(); transIter != state->transitions.end();) {
				Transition* transition = *transIter++;

				/* never select history or initial transitions automatically */
				if unlikely(transition->type & (USCXML_TRANS_HISTORY | USCXML_TRANS_INITIAL))
					continue;

				/* is it spontaneous with an event or vice versa? */
				if ((transition->event.size() == 0 && _event) ||
				        (transition->event.size() != 0 && !_event))
					continue;

				/* check whether it is explicitly conflicting or compatible, calculate if neither */
				if (_flags & USCXML_CTX_TRANSITION_FOUND) {
					BENCHMARK("select transitions conflict & compatible calc");

					if (_conflicting[transition->postFixOrder]) {
						// this transition is explicitly conflicting
						continue;
					}
					if (!_compatible[transition->postFixOrder]) {
						// it is not explicitly compatible, we know nothing!
						BENCHMARK("select transitions conflict & compatible calc no entry");

						bool conflicts = false;
						for (auto enabledTrans : _transSet) {
							if (enabledTrans->compatible.find(transition->postFixOrder) != enabledTrans->compatible.end() ||
							        (enabledTrans->conflicting.find(transition->postFixOrder) != enabledTrans->conflicting.end())) {
								continue;
							}

							std::pair<uint32_t, uint32_t> exit1 = getExitSet(transition);
							std::pair<uint32_t, uint32_t> exit2 = getExitSet(enabledTrans);

							if (exit1.first != 0 && exit2.first != 0 && // empty domain
							        ((exit1.first <= exit2.first && exit1.second >= exit2.first) ||
							         (exit2.first <= exit1.first && exit2.second >= exit1.first))) {
								// it is conflicting!
//                                assert(uscxml::conflicts(t1, t2, _scxml));
								transition->conflicting.insert(enabledTrans->postFixOrder);
								enabledTrans->conflicting.insert(transition->postFixOrder);
								conflicts = true;
								break;
							} else {
//                                assert(!uscxml::conflicts(t1, t2, _scxml));
								transition->compatible.insert(enabledTrans->postFixOrder);
								enabledTrans->compatible.insert(transition->postFixOrder);
							}
						}
						if (conflicts)
							continue;
					}
				}

				/* is it matched? */
				if (_event && !_callbacks->isMatched(_event, transition->event))
					continue;

				/* is it enabled? */
				if (transition->cond.size() > 0 && !_callbacks->isTrue(transition->cond))
					continue;

				// This transition is fine and ought to be taken!

				/* update conflicting and compatible transitions */
				if (_flags & USCXML_CTX_TRANSITION_FOUND) {
					BENCHMARK("select transitions conflict & compatible update");

					/* remove all compatible transitions not listed in ours */
					size_t i = _compatible.find_first();
					while(i != boost::dynamic_bitset<BITSET_BLOCKTYPE>::npos) {
						if (transition->compatible.find(i) == transition->compatible.end()) {
							_compatible[i] = false;
						}
						i = _compatible.find_next(i);
					}

					/* add all conflicting transitions listed in ours */
					for (auto conflict : transition->conflicting) {
						_conflicting[conflict] = true;
					}

				} else {
					/* Very first transition added to optimally transition set */
					for (auto compatible : transition->compatible) {
						_compatible[compatible] = true;
					}
					for (auto conflict : transition->conflicting) {
						_conflicting[conflict] = true;
					}
				}

				/* remember that we found a transition */
				_flags |= USCXML_CTX_TRANSITION_FOUND;

				/* states that are directly targeted (complete as entry-set later) */
				_targetSet.insert(transition->target.begin(), transition->target.end());

				/* lazily initialize exit set */
				if (transition->exitSet.first == 0 && transition->exitSet.second == 0) {
//                    DOMElement* tmp = getTransitionDomain(transition->element, _scxml);
//                    State* domain1 = tmp == NULL ? NULL : (State*)tmp->getUserData(X("uscxmlState"));
//                    uint32_t domain2 = getTransitionDomain(transition);
//                    assert(domain1 == NULL ? domain2 == std::numeric_limits<uint32_t>::max() : domain1->documentOrder == domain2);

//                    std::pair<uint32_t, uint32_t> orig = getExitSetCached(transition->element, _scxml);
					transition->exitSet = getExitSet(transition);
//                    assert(transition->exitSet == orig);
				}

				/* states that will be left */
				for (auto config : _configuration) {
					if (config->documentOrder >= transition->exitSet.first && config->documentOrder <= transition->exitSet.second) {
						_exitSet.insert(config);
					}
				}
				_transSet.insert(transition);

				// break and exit loop if we are at the end
				if (stateIter == _configurationPostFix.end())
					break;

				/* move to next possible state that can have optimally enabled transitions */
				auto nextIter = stateIter;
				nextIter++; // advance by one
				while(nextIter != _configurationPostFix.end() && *nextIter == (*stateIter)->parent) {
					// advance until we found a non-ancestor
					nextIter++;
					stateIter++;
				}

				break; // next state
			}
		}
//        std::cout << "." << iters << std::flush;
	}

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
	printStateNames(_targetSet);
#endif

#ifdef USCXML_VERBOSE
	std::cerr << "ExitSet: ";
	printStateNames(_exitSet);
#endif


	/* REMEMBER_HISTORY: */
	{
		BENCHMARK("remember history");

		for (auto state : _states) {
			if likely(USCXML_STATE_MASK(state->type) != USCXML_STATE_HISTORY_SHALLOW &&
			          USCXML_STATE_MASK(state->type) != USCXML_STATE_HISTORY_DEEP)
				continue;

			if likely(_exitSet.find(state->parent) == _exitSet.end())
				continue;

			/* a history state whose parent is about to be exited */
			for (auto completion : state->completion) {
				if (_configuration.find(completion) != _configuration.end()) {
					_history.insert(completion);
				} else {
					_history.erase(completion);
				}
			}
		}
	}

#ifdef USCXML_VERBOSE
	std::cerr << "History: ";
	printStateNames(_history);
#endif

ESTABLISH_ENTRYSET:
	/* calculate new entry set */
	_entrySet = _targetSet;

#ifdef USCXML_VERBOSE
	std::cerr << "Targets: ";
	printStateNames(_targetSet);
#endif

	/* make sure iterators are not invalidated, TODO: we can know the actual maximum number by syntactic analysis */
	_entrySet.reserve(_states.size());

	/* iterate for ancestors */
	{
		BENCHMARK("add ancestors");
		// running from back to front allows us to add parents only due to document order
		for (auto stateIter = _entrySet.end() ; stateIter != _entrySet.begin() ; /* Do nothing */ ) {
			--stateIter;
			if ((*stateIter)->parent) {
				stateIter = ++(_entrySet.insert((*stateIter)->parent).first);
			}
		}
	}

	/* iterate for descendants */
	{
		BENCHMARK("add descendants");
		// we cannot use the simplified for loop as inserting will invalidate those iterators
		for (auto stateIter = _entrySet.begin(); stateIter != _entrySet.end(); stateIter++ ) {
			State* state = *stateIter;

			switch (USCXML_STATE_MASK(state->type)) {
			case USCXML_STATE_FINAL:
			case USCXML_STATE_ATOMIC:
				break;

			case USCXML_STATE_PARALLEL: {
				BENCHMARK("add descendants parallel");
				_entrySet.insert(state->completion.begin(), state->completion.end());
				break;
			}

			case USCXML_STATE_HISTORY_SHALLOW:
			case USCXML_STATE_HISTORY_DEEP: {
				BENCHMARK("add descendants history");
				if (_configuration.find(state->parent) == _configuration.end() &&
				        !intersects(state->completion.begin(), state->completion.end(), _history.begin(), _history.end())) {

					/* nothing set for history, look for a default transition */
					for (auto transition : state->transitions) {
						_entrySet.insert(transition->target.begin(), transition->target.end());

						if(USCXML_STATE_MASK(state->type) == USCXML_STATE_HISTORY_DEEP &&
						        !intersects(transition->target.begin(), transition->target.end(), state->children.begin(), state->children.end())) {

							// add all the target's ancestors
							for (auto target : transition->target) {
#if 1
								_entrySet.insert(target->ancestors.begin(), target->ancestors.end());
#else
								State* anc = target->parent;
								while(anc != NULL && _entrySet.find(anc) == _entrySet.end()) {
									_entrySet.insert(anc);
									anc = anc->parent;
								}
#endif
							}
						}
						_transSet.insert(transition);
						break;
					}
				} else {
					_tmpStates = state->completion;
					for (auto iter = _tmpStates.begin(); iter != _tmpStates.end();) {
						if (_history.find(*iter) == _history.end()) {
							iter = _tmpStates.erase(iter);
						} else {
							iter++;
						}
					}
					_entrySet.insert(_tmpStates.begin(), _tmpStates.end());

					if (state->type == (USCXML_STATE_HAS_HISTORY | USCXML_STATE_HISTORY_DEEP)) {
						/* a deep history state with nested histories -> more completion */
						for (auto histState : state->completion) {
							if (!(histState->type & USCXML_STATE_HAS_HISTORY))
								continue;

							if (_entrySet.find(histState) == _entrySet.end())
								continue;

							for (auto histChild : histState->children) {
								if ((USCXML_STATE_MASK(histChild->type) == USCXML_STATE_HISTORY_DEEP ||
								        USCXML_STATE_MASK(histChild->type) == USCXML_STATE_HISTORY_SHALLOW)) {
									// We can leverage that deep history assignments are already completed and skip a few states in outer loop
									stateIter = _entrySet.insert(histChild).first;
								}
							}
						}
					}
				}
				break;
			}

			case USCXML_STATE_INITIAL: {
				BENCHMARK("add descendants initial");
				for (auto transition : state->transitions) {
					_transSet.insert(transition); // remember transition for onentry later

					for (auto target : transition->target) {
						_entrySet.insert(target);
						// add all states between target and this state
#if 1
						_entrySet.insert(target->ancestors.begin(), target->ancestors.end());
#else
						State* anc = target->parent;
						while(anc != NULL && anc != state) {
							_entrySet.insert(anc);
							anc = anc->parent;
						}
#endif
					}
				}
				break;
			}

			case USCXML_STATE_COMPOUND: {
				BENCHMARK("add descendants compound");

				/* Compound state may already be complete */
				{
					BENCHMARK("add descendants compound intersect entry/child");
					for (auto child : state->children) {
						/* one child is already in entry_set */
						if (_entrySet.find(child) != _entrySet.end())
							goto NEXT_DESCENDANT;
						/* one child is already active and not left */
						if (_exitSet.find(child) == _exitSet.end() && _configuration.find(child) != _configuration.end())
							goto NEXT_DESCENDANT;
					}
				}

				// completion of a compound maybe multiple states via initial attribute
				_entrySet.insert(state->completion.begin(), state->completion.end());

				/* deep completion */
				{
					BENCHMARK("add descendants compound deep completion");
					for (auto completion : state->completion) {

						if (std::binary_search(state->children.begin(), state->children.end(), completion))
							continue;

						// add deep completions ancestors
#if 1
						_entrySet.insert(completion->ancestors.begin(), completion->ancestors.end());
#else
						State* anc = completion->parent;
						while(anc != NULL && anc != state) {
							_entrySet.insert(anc);
							anc = anc->parent;
						}
#endif
					}
				}
				break;
			}

			}
NEXT_DESCENDANT:
			;
		}
	}

#ifdef USCXML_VERBOSE
	std::cerr << "Entering: ";
	printStateNames(_entrySet);
#endif

	/* EXIT_STATES: */
	{
		BENCHMARK("exit states");
		for (auto stateIter = _exitSet.end() ; stateIter != _exitSet.begin() ; /* Do nothing */ ) {
			State* state = *(--stateIter);

			USCXML_MONITOR_CALLBACK2(monitors, beforeExitingState, state->name, state->element);

			/* call all on exit handlers */
			for (auto exitIter = state->onExit.begin(); exitIter != state->onExit.end(); exitIter++) {
				try {
					_callbacks->process(*exitIter);
				} catch (...) {
					// do nothing and continue with next block
				}
			}

			_configuration.erase(state);
			_configurationPostFix.erase(state);
			USCXML_MONITOR_CALLBACK2(monitors, afterExitingState, state->name, state->element);

		}
	}

	/* TAKE_TRANSITIONS: */
	{
		BENCHMARK("take transitions");
		for (auto transition : _transSet) {
			if ((transition->type & (USCXML_TRANS_HISTORY | USCXML_TRANS_INITIAL)) == 0) {
				USCXML_MONITOR_CALLBACK1(monitors, beforeTakingTransition, transition->element);

				if (transition->onTrans != NULL) {

					/* call executable content in non-history, non-initial transition */
					try {
						_callbacks->process(transition->onTrans);
					} catch (...) {
						// do nothing and continue with next block
					}
				}

				USCXML_MONITOR_CALLBACK1(monitors, afterTakingTransition, transition->element);
			}
		}
	}

	// remove active state from enter states
	for (auto config : _configuration) {
		if (_entrySet.find(config) != _entrySet.end())
			_entrySet.erase(config);
	}

	/* ENTER_STATES: */
	{
		BENCHMARK("enter states");
		for (auto state : _entrySet) {

			/* these are no proper states */
			if unlikely(USCXML_STATE_MASK(state->type) == USCXML_STATE_HISTORY_DEEP ||
			            USCXML_STATE_MASK(state->type) == USCXML_STATE_HISTORY_SHALLOW ||
			            USCXML_STATE_MASK(state->type) == USCXML_STATE_INITIAL) {
				continue;
			}

			USCXML_MONITOR_CALLBACK2(monitors, beforeEnteringState, state->name, state->element);

			_configuration.insert(state);
			_configurationPostFix.insert(state);

			/* initialize data */
			if (state->data.size() > 0) {
				if (_initializedData.find(state) == _initializedData.end()) {
					for (auto dataIter = state->data.begin(); dataIter != state->data.end(); dataIter++) {
						_callbacks->initData(*dataIter);
					}
					_initializedData.insert(state);
				}
			}

			/* call all on entry handlers */
			for (auto onEntry : state->onEntry) {
				try {
					_callbacks->process(onEntry);
				} catch (...) {
					// do nothing and continue with next block
				}
			}

			USCXML_MONITOR_CALLBACK2(monitors, afterEnteringState, state->name, state->element);

			/* take history and initial transitions */
			for (auto child : state->children) {
				if (child->type != USCXML_STATE_INITIAL &&
				        child->type != USCXML_STATE_HISTORY_DEEP &&
				        child->type != USCXML_STATE_HISTORY_SHALLOW)
					continue;

				for (auto transition : child->transitions) {
					if (!(transition->type & (USCXML_TRANS_HISTORY | USCXML_TRANS_INITIAL)) ||
					        _transSet.find(transition) == _transSet.end())
						continue;

					USCXML_MONITOR_CALLBACK1(monitors, beforeTakingTransition, transition->element);

					/* call executable content in transition */
					if (transition->onTrans != NULL) {
						try {
							_callbacks->process(transition->onTrans);
						} catch (...) {
							// do nothing and continue with next block
						}
					}

					USCXML_MONITOR_CALLBACK1(monitors, afterTakingTransition, transition->element);
				}

			}

			/* handle final states */
			if unlikely(USCXML_STATE_MASK(state->type) == USCXML_STATE_FINAL) {
				BENCHMARK("enter states final")
				if unlikely(state->parent == _states[0]) {
					// only the topmost scxml is an ancestor
					_flags |= USCXML_CTX_TOP_LEVEL_FINAL;
				} else {
					/* raise done event */
					_callbacks->raiseDoneEvent(state->parent->element, state->doneData);
				}

				/**
				 * are we the last final state to leave a parallel state?:
				 * 1. Gather all parallel states in our ancestor chain
				 * 2. Find all states for which these parallels are ancestors
				 * 3. Iterate all active final states and remove their ancestors
				 * 4. If a state remains, not all children of a parallel are final
				 */
				{
					BENCHMARK("enter states final parallel")

					State* anc = state->parent;
					while(anc != NULL) {
						if (USCXML_STATE_MASK(anc->type) == USCXML_STATE_PARALLEL) {
							if (isInFinal(anc)) {
								_callbacks->raiseDoneEvent(anc->element, anc->doneData);
							} else {
								break; // ancestors cannot be final either
							}
						}
						anc = anc->parent;
					}
				}
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

bool LargeMicroStep::isInFinal(const State* state) {
	switch (USCXML_STATE_MASK(state->type)) {
	case USCXML_STATE_FINAL:
		/* a final state is final */
		return true;

	case USCXML_STATE_ATOMIC:
		return false;

	case USCXML_STATE_PARALLEL:
		for (auto child : state->children) {
			if (!isInFinal(child))
				return false;
		}
		return true;

	case USCXML_STATE_INITIAL:
		return false;

	case USCXML_STATE_COMPOUND:
		for (auto child : state->children) {
			if (_configuration.find(child) != _configuration.end()) {
				return isInFinal(child);
				break;
			}
		}
		return true;

	default:
		// history
		return true;
		break;
	}
	return false;
}

void LargeMicroStep::resortStates(DOMElement* element, const X& xmlPrefix) {

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

std::pair<uint32_t, uint32_t> LargeMicroStep::getExitSet(const Transition* transition) {
	if (_exitSetCache.find(transition->postFixOrder) == _exitSetCache.end()) {
		std::pair<uint32_t, uint32_t> statesToExit;
		uint32_t domain = getTransitionDomain(transition);
		if (domain == std::numeric_limits<uint32_t>::max())
			return statesToExit;

		State* domainState = _states[domain];

		// start of exit set
		statesToExit.first = domainState->documentOrder + 1; // do not include domain itself

		// end of exit set
		XERCESC_NS::DOMElement* sibling = domainState->element->getNextElementSibling();
		while(sibling && !isState(sibling))
			sibling = sibling->getNextElementSibling();
		if (sibling) {
			State* siblingState = (State*)sibling->getUserData(X("uscxmlState"));
			statesToExit.second = siblingState->documentOrder - 1;
		} else {
			statesToExit.second = _states.size() - 1;
		}
		_exitSetCache[transition->postFixOrder] = statesToExit;
		return statesToExit;
	}
	return _exitSetCache[transition->postFixOrder];
}

uint32_t LargeMicroStep::getTransitionDomain(const Transition* transition) {
	if (transition->target.size() == 0)
		return std::numeric_limits<uint32_t>::max();

	bool internal = (HAS_ATTR(transition->element, kXMLCharType) ? ATTR(transition->element, kXMLCharType) == "internal" : false);
	if (internal && USCXML_STATE_MASK(transition->source->type) == USCXML_STATE_COMPOUND) {
		for (auto target : transition->target) {
			if (target->ancestors.find(transition->source) == target->ancestors.end()) {
				goto BREAK_LOOP;
			}
		}
		return transition->source->documentOrder;
	}
BREAK_LOOP:

	// find LCCA
	uint32_t ancestor = std::numeric_limits<uint32_t>::max();

	// reverse walk up!
	for(auto ancIter = transition->source->ancestors.rbegin(); ancIter != transition->source->ancestors.rend(); ancIter++) {
		State* anc = *ancIter;

		// LCCA has to be a compound
		if (!(USCXML_STATE_MASK(anc->type) == USCXML_STATE_COMPOUND))
			continue;

		// that contains all states
		for (auto target : transition->target) {
			if (target->ancestors.find(anc) == target->ancestors.end()) {
				goto NEXT_ANCESTOR;
			}
		}
		ancestor = anc->documentOrder;
		break;
NEXT_ANCESTOR:
		;
	}

	// none found - take uppermost root as ancestor
	if (ancestor == std::numeric_limits<uint32_t>::max())
		return 0;
	return ancestor;
}

}
