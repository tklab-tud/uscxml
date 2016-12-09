/**
 *  @file
 *  @author     2012-2015 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#include "uscxml/transform/ChartToC.h"
#include <iostream>
#include "uscxml/util/UUID.h"
#include "uscxml/util/Predicates.h"
#include "uscxml/util/MD5.hpp"
#include "uscxml/util/DOM.h"
#include "uscxml/util/String.h"
#include <math.h>
#include <boost/algorithm/string.hpp>
#include "uscxml/interpreter/Logging.h"

#include <algorithm>
#include <iomanip>

namespace uscxml {

using namespace XERCESC_NS;


// many more tricks: https://graphics.stanford.edu/~seander/bithacks.html

Transformer ChartToC::transform(const Interpreter& other) {
	ChartToC* c2c = new ChartToC(other);

	return std::shared_ptr<TransformerImpl>(c2c);
}

ChartToC::ChartToC(const Interpreter& other) : TransformerImpl(other), _topMostMachine(NULL), _parentMachine(NULL) {

	std::stringstream ss;
	ss << _document;

	_md5 = md5(ss.str());
	_prefix = "_uscxml_" + _md5.substr(0, 8) + "_";
	_allMachines.push_back(this);

	prepare();
	findNestedMachines();

	if (_extensions.find("prefix") != _extensions.end()) {
		_prefixes = new std::list<std::string>();
		std::pair<std::multimap<std::string, std::string>::iterator,
		    std::multimap<std::string, std::string>::iterator> keyRange = _extensions.equal_range("prefix");
		for (std::multimap<std::string, std::string>::iterator iter = keyRange.first; iter != keyRange.second; ++iter) {
			_prefixes->push_back(iter->second);
		}
	}

}

void ChartToC::setHistoryCompletion() {

	std::list<DOMElement*> histories = DOMUtils::inPostFixOrder({ XML_PREFIX(_scxml).str() + "history" }, _scxml);

	std::list<DOMElement*> covered;
	std::list<DOMElement*> perParentcovered;
	DOMNode* parent = NULL;

	for (auto histIter = histories.begin(); histIter != histories.end(); histIter++) {
		DOMElement* history = *histIter;
		std::list<DOMElement*> completion;

		if (parent != history->getParentNode()) {
			covered.insert(covered.end(), perParentcovered.begin(), perParentcovered.end());
			perParentcovered.clear();
			parent = history->getParentNode();
		}

		bool deep = (HAS_ATTR(history, "type") && iequals(ATTR(history, "type"), "deep"));
		for (auto stateIter = _states.begin(); stateIter != _states.end(); stateIter++) {
			DOMElement* state = *stateIter;
			if (state == history)
				continue;

			if (DOMUtils::isDescendant(state, history->getParentNode()) && isHistory(state)) {
				history->setAttribute(X("hasHistoryChild"), X("yes"));
			}

			if (DOMUtils::isMember(state, covered))
				continue;

			if (deep) {
				if (DOMUtils::isDescendant(state, history->getParentNode()) && !isHistory(state)) {
					completion.push_back(state);
				}
			} else {
				if (state->getParentNode() == history->getParentNode() && !isHistory(state)) {
					completion.push_back(state);
				}
			}
		}
		perParentcovered.insert(perParentcovered.end(), completion.begin(), completion.end());

		std::string completionBools;
		for (size_t j = 0; j < _states.size(); j++) {
			if (DOMUtils::isMember(_states[j], completion)) {
				completionBools += "1";
			} else {
				completionBools += "0";
			}
		}
		history->setAttribute(X("completionBools"), X(completionBools));
	}
}

void ChartToC::resortStates(DOMNode* node) {
	if (node->getNodeType() != DOMNode::ELEMENT_NODE)
		return;

	/**
	  initials
	  deep histories
	  shallow histories
	  everything else
	 */

	DOMElement* element = static_cast<DOMElement*>(node);

	// shallow history states to top
	DOMNode* child = element->getFirstChild();
	while(child) {
		resortStates(child);
		if (child->getNodeType() == DOMNode::ELEMENT_NODE &&
		        TAGNAME_CAST(child) == XML_PREFIX(node).str() + "history" &&
		        (!HAS_ATTR(element, "type") || iequals(ATTR(element, "type"), "shallow"))) {
			DOMNode* tmp = child->getNextSibling();
			if (child != element->getFirstChild()) {
				element->insertBefore(child, element->getFirstChild());
			}
			child = tmp;
		} else {
			child = child->getNextSibling();
		}
	}

	// deep history states to top
	child = element->getFirstChild();
	while(child) {
		resortStates(child);
		if (child->getNodeType() == DOMNode::ELEMENT_NODE &&
		        TAGNAME_CAST(child) == XML_PREFIX(node).str() + "history" &&
		        HAS_ATTR(element, "type") &&
		        iequals(ATTR(element, "type"), "deep")) {

			DOMNode* tmp = child->getNextSibling();
			if (child != element->getFirstChild()) {
				element->insertBefore(child, element->getFirstChild());
			}
			child = tmp;
		} else {
			child = child->getNextSibling();
		}
	}

	// initial states on top of histories even
	child = element->getFirstChild();
	while(child) {
		resortStates(child);
		if (child->getNodeType() == DOMNode::ELEMENT_NODE && TAGNAME_CAST(child) == XML_PREFIX(node).str() + "initial") {
			DOMNode* tmp = child->getNextSibling();
			if (child != element->getFirstChild()) {
				element->insertBefore(child, element->getFirstChild());
			}
			child = tmp;
		} else {
			child = child->getNextSibling();
		}
	}

}

void ChartToC::setStateCompletion() {
	setHistoryCompletion();

	for (size_t i = 0; i < _states.size(); i++) {
		DOMElement* state(_states[i]);

		if (isHistory(state)) {
			// we already did in setHistoryCompletion
			continue;
		}

		std::list<DOMElement*> completion;

		if (isParallel(state)) {
			completion = getChildStates(state);

		} else if (HAS_ATTR(state, "initial")) {
			completion = getStates(tokenize(ATTR(state, "initial")), _scxml);

		} else {
			std::list<DOMElement*> initElems = DOMUtils::filterChildElements(XML_PREFIX(state).str() + "initial", state);
			if(initElems.size() > 0) {
				// initial element is first child
				completion.push_back(initElems.front());
			} else {
				// first child state
				std::list<DOMElement*> initStates;
				DOMNodeList* childs = state->getChildNodes();
				for (size_t i = 0; i < childs->getLength(); i++) {
					if (childs->item(i)->getNodeType() != DOMNode::ELEMENT_NODE)
						continue;
					DOMElement* childElem = static_cast<DOMElement*>(childs->item(i));
					if (isState(childElem)) {
						completion.push_back(childElem);
						break;
					}
				}
			}
		}

		std::string completionBools;
		for (size_t j = 0; j < _states.size(); j++) {
			if (DOMUtils::isMember(_states[j], completion)) {
				completionBools += "1";
			} else {
				completionBools += "0";
			}
		}
		state->setAttribute(X("completionBools"), X(completionBools));
	}
}

void ChartToC::prepare() {

	// make sure initial and history elements always precede propoer states
	resortStates(_scxml);

	std::list<XERCESC_NS::DOMElement*> tmp = DOMUtils::inDocumentOrder({
		XML_PREFIX(_scxml).str() + "scxml",
		XML_PREFIX(_scxml).str() + "state",
		XML_PREFIX(_scxml).str() + "final",
		XML_PREFIX(_scxml).str() + "history",
		XML_PREFIX(_scxml).str() + "initial",
		XML_PREFIX(_scxml).str() + "parallel"
	}, _scxml);
	_states.insert(_states.end(), tmp.begin(), tmp.end());

	// set states' document order and parent attribute
	for (size_t i = 0; i < _states.size(); i++) {
		DOMElement* state(_states[i]);
		state->setAttribute(X("documentOrder"), X(toStr(i)));
		if (state->getParentNode()->getNodeType() == DOMNode::ELEMENT_NODE &&
		        HAS_ATTR_CAST(state->getParentNode(), "documentOrder")) {
			state->setAttribute(X("parent"), X(ATTR_CAST(state->getParentNode(), "documentOrder")));
		}

		// set the states' children and whether it has a history
		std::string childBools;
		bool hasHistoryChild = false;
		for (size_t j = 0; j < _states.size(); j++) {
			if (_states[j]->getParentNode() == state) {
				if (isHistory(static_cast<DOMElement*>(_states[j]))) {
					hasHistoryChild = true;
				}
				childBools += "1";
			} else {
				childBools += "0";
			}
		}
		state->setAttribute(X("childBools"), X(childBools));
		if (hasHistoryChild) {
			state->setAttribute(X("hasHistoryChild"), X("yes"));
		}

		// ancestors
		std::string ancBools;
		for (size_t j = 0; j < _states.size(); j++) {
			if (DOMUtils::isDescendant(state, _states[j])) {
				ancBools += "1";
			} else {
				ancBools += "0";
			}
		}
		state->setAttribute(X("ancBools"), X(ancBools));

	}


	// set transitions' document order and source attribute
	tmp = DOMUtils::inDocumentOrder({ XML_PREFIX(_scxml).str() + "transition" }, _scxml);
	size_t index = 0;
	for (auto transIter = tmp.begin(); transIter != tmp.end(); transIter++, index++) {
		DOMElement* transition = *transIter;
		transition->setAttribute(X("documentOrder"), X(toStr(index)));
		if (transition->getParentNode()->getNodeType() == DOMNode::ELEMENT_NODE &&
		        HAS_ATTR_CAST(transition->getParentNode(), "documentOrder")) {
			transition->setAttribute(X("source"), X(ATTR_CAST(transition->getParentNode(), "documentOrder")));
		}
	}

	// set transitions' postfix order attribute
	tmp = DOMUtils::inPostFixOrder({ XML_PREFIX(_scxml).str() + "transition" }, _scxml);
	_transitions.insert(_transitions.end(), tmp.begin(), tmp.end());

	for (size_t i = 0; i < _transitions.size(); i++) {
		DOMElement* transition(_transitions[i]);
		transition->setAttribute(X("postFixOrder"), X(toStr(i)));

		// and exit set
		std::string exitSetBools;
		std::list<DOMElement*> exitSet = getExitSet(transition, _scxml);
		for (unsigned int j = 0; j < _states.size(); j++) {
			DOMElement* state(_states[j]);
			if (DOMUtils::isMember(state, exitSet)) {
				exitSetBools += "1";
			} else {
				exitSetBools += "0";
			}
		}
		transition->setAttribute(X("exitSetBools"), X(exitSetBools));

		// and conflicts
		std::string conflictBools;
		for (unsigned int j = 0; j < _transitions.size(); j++) {
			DOMElement* t2(_transitions[j]);
			if (DOMUtils::hasIntersection(getExitSet(transition, _scxml), getExitSet(t2, _scxml)) ||
			        (getSourceState(transition) == getSourceState(t2)) ||
			        (DOMUtils::isDescendant(getSourceState(transition), getSourceState(t2))) ||
			        (DOMUtils::isDescendant(getSourceState(t2), getSourceState(transition)))) {
				conflictBools += "1";
			} else {
				conflictBools += "0";
			}
		}
		transition->setAttribute(X("conflictBools"), X(conflictBools));

		// and target
		if (HAS_ATTR(transition, "target")) {
			std::list<std::string> targets = tokenize(ATTR(transition, "target"));

			std::string targetBools;
			for (size_t j = 0; j < _states.size(); j++) {
				DOMElement* state(_states[j]);

				if (HAS_ATTR(state, "id") &&
				        std::find(targets.begin(), targets.end(), escape(ATTR(state, "id"))) != targets.end()) {
					targetBools += "1";
				} else {
					targetBools += "0";
				}
			}
			transition->setAttribute(X("targetBools"), X(targetBools));

		}
	}
	// leave transitions in postfix order



	// set the completion of states and responsibility of history elements
	setStateCompletion();

	// how many bits do we need to represent the state array?
	std::string seperator;
	_stateCharArraySize = ceil((float)_states.size() / (float)8);
	_stateCharArrayInit = "{";
	for (size_t i = 0; i < _stateCharArraySize; i++) {
		_stateCharArrayInit += seperator + "0";
		seperator = ", ";
	}
	_stateCharArrayInit += "}";

	if (false) {
	} else if (_states.size() < (1UL << 8)) {
		_stateDataType = "uint8_t";
	} else if (_states.size() < (1UL << 16)) {
		_stateDataType = "uint16_t";
	} else if (_states.size() < (1UL << 32)) {
		_stateDataType = "uint32_t";
	} else {
		_stateDataType = "uint64_t";
	}

	seperator = "";
	_transCharArraySize = ceil((float)_transitions.size() / (float)8);
	_transCharArrayInit = "{";
	for (size_t i = 0; i < _transCharArraySize; i++) {
		_transCharArrayInit += seperator + "0";
		seperator = ", ";
	}
	_transCharArrayInit += "}";

	if (false) {
	} else if (_transitions.size() < (1UL << 8)) {
		_transDataType = "uint8_t";
	} else if (_transitions.size() < (1UL << 16)) {
		_transDataType = "uint16_t";
	} else if (_transitions.size() < (1UL << 32)) {
		_transDataType = "uint32_t";
	} else {
		_transDataType = "uint64_t";
	}

}

void ChartToC::writeTo(std::ostream& stream) {

	stream << "/**" << std::endl;
	stream << "  Generated from source:" << std::endl;
	stream << "  " << (std::string)_baseURL << std::endl;
	stream << "*/" << std::endl;
	stream << std::endl;

	writeIncludes(stream);
	writeMacros(stream);
	writeTypes(stream);
	writeForwardDeclarations(stream);

	for (std::list<ChartToC*>::iterator machIter = _allMachines.begin(); machIter != _allMachines.end(); machIter++) {
		(*machIter)->writeElementInfo(stream);
		(*machIter)->writeExecContentFinalize(stream);
		(*machIter)->writeElementInfoInvocation(stream);
		(*machIter)->writeExecContent(stream);
		(*machIter)->writeStates(stream);
		(*machIter)->writeTransitions(stream);
		(*machIter)->writeMachineInfo(stream);
	}
	writeHelpers(stream);
	writeFSM(stream);

	//    http://stackoverflow.com/questions/2525310/how-to-define-and-work-with-an-array-of-bits-in-c

}

void ChartToC::writeForwardDeclarations(std::ostream& stream) {
	stream << "/* forward declare machines to allow references */" << std::endl;
	for (std::list<ChartToC*>::iterator machIter = _allMachines.begin(); machIter != _allMachines.end(); machIter++) {
		stream << "extern const uscxml_machine " << (*machIter)->_prefix << "_machine;" << std::endl;
	}
	stream << std::endl;
}

void ChartToC::findNestedMachines() {
	std::list<DOMElement*> invokes = DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "invoke", _scxml, true);

	for (auto invIter = invokes.begin(); invIter != invokes.end(); invIter++) {
		DOMElement* invoke = *invIter;

		if(!areFromSameMachine(invoke, _scxml))
			continue;

		if (HAS_ATTR(invoke, "type") &&
		        ATTR(invoke, "type") != "scxml" &&
		        ATTR(invoke, "type") != "http://www.w3.org/TR/scxml/")
			continue;

		ChartToC* c2c = NULL;
		if (HAS_ATTR(invoke, "src")) {

			URL srcURL(ATTR(invoke, "src"));
			if (!srcURL.isAbsolute()) {
				srcURL = URL::resolve(srcURL, _baseURL);
			}
			std::string tmp = (std::string)srcURL;
			c2c = new ChartToC(Interpreter::fromURL(tmp));
		} else {
			// is there a nested scxml machine inside?
			std::list<DOMElement*> contents = DOMUtils::filterChildElements(XML_PREFIX(invoke).str() + "content", invoke);
			if (contents.size() == 0)
				continue;
			std::list<DOMElement*> scxmls = DOMUtils::filterChildElements(XML_PREFIX(invoke).str() + "scxml", contents.front());
			if (scxmls.size() == 0)
				continue;

			c2c = new ChartToC(Interpreter::fromElement(scxmls.front(), _baseURL));
			c2c->_name += "." + DOMUtils::idForNode(scxmls.front());
		}

		if (c2c != NULL) {
			invoke->setAttribute(X("md5sum"), X(c2c->_md5));
			ChartToC* topMostMachine = (_topMostMachine == NULL ? this : _topMostMachine);
			c2c->_topMostMachine = topMostMachine;
			c2c->_parentMachine = this;
			_nestedMachines.push_back(c2c);
			topMostMachine->_allMachines.push_back(c2c);
		}
	}
}

void ChartToC::writeIncludes(std::ostream& stream) {
	stream << "#ifndef USCXML_NO_STDTYPES_H" << std::endl;
	stream << "#  include <stdint.h> /* explicit types */" << std::endl;
	stream << "#endif" << std::endl;
	stream << "#include <stddef.h> /* NULL */" << std::endl;
	stream << std::endl;
}

void ChartToC::writeMacros(std::ostream& stream) {
	stream << "#ifndef USCXML_NO_GEN_C_MACROS" << std::endl;
	stream << std::endl;
	stream << "/**" << std::endl;
	stream << " * All macros used for the scxml types and functions" << std::endl;
	stream << " * " << std::endl;
	stream << " * ** IMPORTANT: Make sure to set the following macros prior to including. **" << std::endl;
	stream << " *               They are used to represent the machine in the types to follow" << std::endl;
	stream << " *               and to allocate stack memory during a micro-step function." << std::endl;
	stream << " *               When in doubt, overprovide." << std::endl;
	stream << " * " << std::endl;
	stream << " *    USCXML_NR_STATES_TYPE" << std::endl;
	stream << " *      as the smallest type for positive integers that can contain the" << std::endl;
	stream << " *      largest number of states from an individual state machine. E.g.:" << std::endl;
	stream << " *      < 2^8  states => uint8_t" << std::endl;
	stream << " *      < 2^16 states => uint16_t" << std::endl;
	stream << " *      < 2^32 states => uint32_t" << std::endl;
	stream << " */" << std::endl;
	stream << std::endl;

	stream << "#ifndef USCXML_NR_STATES_TYPE " << std::endl;
	stream << "#  define USCXML_NR_STATES_TYPE " << _stateDataType << std::endl;
	stream << "#endif " << std::endl;
	stream << std::endl;

	stream << "/**" << std::endl;
	stream << " *    USCXML_NR_TRANS_TYPE" << std::endl;
	stream << " *      the same as above but for the number of transitions." << std::endl;
	stream << " */" << std::endl;
	stream << std::endl;

	stream << "#ifndef USCXML_NR_TRANS_TYPE " << std::endl;
	stream << "#  define USCXML_NR_TRANS_TYPE " << _transDataType << std::endl;
	stream << "#endif " << std::endl;
	stream << std::endl;

	stream << "/** " << std::endl;
	stream << " *    USCXML_MAX_NR_STATES_BYTES" << std::endl;
	stream << " *      the smallest multiple of 8 that, if multiplied by 8," << std::endl;
	stream << " *      is larger than USCXML_NR_STATES_TYPE, e.g:" << std::endl;
	stream << " *      1-8   states => 1" << std::endl;
	stream << " *      9-16  states => 2" << std::endl;
	stream << " *      17-24 states => 3" << std::endl;
	stream << " *      25-32 states => 4" << std::endl;
	stream << " *      ..." << std::endl;
	stream << " */" << std::endl;
	stream << std::endl;

	stream << "#ifndef USCXML_MAX_NR_STATES_BYTES " << std::endl;
	stream << "#  define USCXML_MAX_NR_STATES_BYTES " << (std::max)((size_t)1, _stateCharArraySize) << std::endl;
	stream << "#endif " << std::endl;
	stream << std::endl;

	stream << "/**" << std::endl;
	stream << " *    USCXML_MAX_NR_TRANS_BYTES" << std::endl;
	stream << " *      same as above but for transitions." << std::endl;
	stream << " */" << std::endl;
	stream << std::endl;

	stream << "#ifndef USCXML_MAX_NR_TRANS_BYTES " << std::endl;
	stream << "#  define USCXML_MAX_NR_TRANS_BYTES " << (std::max)((size_t)1, _transCharArraySize) << std::endl;
	stream << "#endif " << std::endl;
	stream << std::endl;

	stream << "/**" << std::endl;
	stream << " *    USCXML_NUMBER_STATES / USCXML_NUMBER_TRANS" << std::endl;
	stream << " *      Per default the number of states / transitions is retrieved from the machine" << std::endl;
	stream << " *      info in the uscxml_ctx struct, but you can also hard-code it per macro." << std::endl;
	stream << " */" << std::endl;
	stream << std::endl;

	stream << "#ifndef USCXML_NUMBER_STATES" << std::endl;
	stream << "#  define USCXML_NUMBER_STATES (ctx->machine->nr_states)" << std::endl;
	stream << "#endif" << std::endl;
	stream << std::endl;

	stream << "#ifndef USCXML_NUMBER_TRANS" << std::endl;
	stream << "#  define USCXML_NUMBER_TRANS (ctx->machine->nr_transitions)" << std::endl;
	stream << "#endif" << std::endl;
	stream << std::endl;

	stream << "/**" << std::endl;
	stream << " *    USCXML_GET_STATE / USCXML_GET_TRANS" << std::endl;
	stream << " *      Per default an individual state or transitions is retrieved from the machine" << std::endl;
	stream << " *      info in the uscxml_ctx struct, but you can also hard-code it per macro." << std::endl;
	stream << " */" << std::endl;
	stream << std::endl;

	stream << "#ifndef USCXML_GET_STATE" << std::endl;
	stream << "#  define USCXML_GET_STATE(i) (ctx->machine->states[i])" << std::endl;
	stream << "#endif" << std::endl;
	stream << std::endl;

	stream << "#ifndef USCXML_GET_TRANS" << std::endl;
	stream << "#  define USCXML_GET_TRANS(i) (ctx->machine->transitions[i])" << std::endl;
	stream << "#endif" << std::endl;
	stream << std::endl;
	stream << std::endl;
	stream << "/* Common macros below */"<< std::endl;
	stream << std::endl;

	stream << "#define BIT_HAS(idx, bitset)   ((bitset[idx >> 3] &  (1 << (idx & 7))) != 0)" << std::endl;
	stream << "#define BIT_SET_AT(idx, bitset)  bitset[idx >> 3] |= (1 << (idx & 7));" << std::endl;
	stream << "#define BIT_CLEAR(idx, bitset)   bitset[idx >> 3] &= (1 << (idx & 7)) ^ 0xFF;" << std::endl;
	stream << std::endl;

	stream << "#ifdef __GNUC__" << std::endl;
	stream << "#  define likely(x)       (__builtin_expect(!!(x), 1))" << std::endl;
	stream << "#  define unlikely(x)     (__builtin_expect(!!(x), 0))" << std::endl;
	stream << "#else" << std::endl;
	stream << "#  define likely(x)       (x)" << std::endl;
	stream << "#  define unlikely(x)     (x)" << std::endl;
	stream << "#endif" << std::endl;
	stream << std::endl;

	stream << "/* error return codes */" << std::endl;
	stream << "#define USCXML_ERR_OK                0" << std::endl;
	stream << "#define USCXML_ERR_IDLE              1" << std::endl;
	stream << "#define USCXML_ERR_DONE              2" << std::endl;
	stream << "#define USCXML_ERR_MISSING_CALLBACK  3" << std::endl;
	stream << "#define USCXML_ERR_FOREACH_DONE      4" << std::endl;
	stream << "#define USCXML_ERR_EXEC_CONTENT      5" << std::endl;
	stream << "#define USCXML_ERR_INVALID_TARGET    6" << std::endl;
	stream << "#define USCXML_ERR_INVALID_TYPE      7" << std::endl;
	stream << "#define USCXML_ERR_UNSUPPORTED       8" << std::endl;
	stream << std::endl;

	stream << "#define USCXML_TRANS_SPONTANEOUS      0x01" << std::endl;
	stream << "#define USCXML_TRANS_TARGETLESS       0x02" << std::endl;
	stream << "#define USCXML_TRANS_INTERNAL         0x04" << std::endl;
	stream << "#define USCXML_TRANS_HISTORY          0x08" << std::endl;
	stream << "#define USCXML_TRANS_INITIAL          0x10" << std::endl;
	stream << std::endl;

	stream << "#define USCXML_STATE_ATOMIC           0x01" << std::endl;
	stream << "#define USCXML_STATE_PARALLEL         0x02" << std::endl;
	stream << "#define USCXML_STATE_COMPOUND         0x03" << std::endl;
	stream << "#define USCXML_STATE_FINAL            0x04" << std::endl;
	stream << "#define USCXML_STATE_HISTORY_DEEP     0x05" << std::endl;
	stream << "#define USCXML_STATE_HISTORY_SHALLOW  0x06" << std::endl;
	stream << "#define USCXML_STATE_INITIAL          0x07" << std::endl;
	stream << "#define USCXML_STATE_HAS_HISTORY      0x80  /* highest bit */" << std::endl;
	stream << "#define USCXML_STATE_MASK(t)     (t & 0x7F) /* mask highest bit */" << std::endl;

	stream << "" << std::endl;
	stream << "#define USCXML_CTX_PRISTINE           0x00" << std::endl;
	stream << "#define USCXML_CTX_SPONTANEOUS        0x01" << std::endl;
	stream << "#define USCXML_CTX_INITIALIZED        0x02" << std::endl;
	stream << "#define USCXML_CTX_TOP_LEVEL_FINAL    0x04" << std::endl;
	stream << "#define USCXML_CTX_TRANSITION_FOUND   0x08" << std::endl;
	stream << "#define USCXML_CTX_FINISHED           0x10" << std::endl;
	stream << std::endl;

	stream << "#define USCXML_ELEM_DATA_IS_SET(data) (data->id != NULL)" << std::endl;
	stream << "#define USCXML_ELEM_DONEDATA_IS_SET(donedata) (donedata->content != NULL || donedata->contentexpr != NULL || donedata->params != NULL)" << std::endl;
	stream << "#define USCXML_ELEM_PARAM_IS_SET(param) (param->name != NULL)" << std::endl;
	stream << "#define USCXML_MACHINE_IS_SET(machine) (machine->nr_states > 0)" << std::endl;
	stream << std::endl;
	stream << "#define USCXML_NO_GEN_C_MACROS" << std::endl;
	stream << "#endif" << std::endl;
	stream << std::endl;
}

void ChartToC::writeTypes(std::ostream& stream) {

	stream << std::endl;
	stream << "#ifndef USCXML_NO_GEN_C_TYPES" << std::endl;
	stream << std::endl;
	stream << "/**" << std::endl;
	stream << " * All types required to represent an SCXML state chart." << std::endl;
	stream << " * Just predefine the USCXML_NO_GEN_C_TYPES macro if you do not need them." << std::endl;
	stream << " */" << std::endl;
	stream << std::endl;

	stream << "typedef struct uscxml_machine uscxml_machine;" << std::endl;
	stream << "typedef struct uscxml_transition uscxml_transition;" << std::endl;
	stream << "typedef struct uscxml_state uscxml_state;" << std::endl;
	stream << "typedef struct uscxml_ctx uscxml_ctx;" << std::endl;
	stream << "typedef struct uscxml_elem_invoke uscxml_elem_invoke;" << std::endl;
	stream << std::endl;

	stream << "typedef struct uscxml_elem_send uscxml_elem_send;" << std::endl;
	stream << "typedef struct uscxml_elem_param uscxml_elem_param;" << std::endl;
	stream << "typedef struct uscxml_elem_data uscxml_elem_data;" << std::endl;
	stream << "typedef struct uscxml_elem_assign uscxml_elem_assign;" << std::endl;
	stream << "typedef struct uscxml_elem_donedata uscxml_elem_donedata;" << std::endl;
	stream << "typedef struct uscxml_elem_foreach uscxml_elem_foreach;" << std::endl;
	stream << std::endl;

	stream << "typedef void* (*dequeue_internal_t)(const uscxml_ctx* ctx);" << std::endl;
	stream << "typedef void* (*dequeue_external_t)(const uscxml_ctx* ctx);" << std::endl;
	stream << "typedef int (*is_enabled_t)(const uscxml_ctx* ctx, const uscxml_transition* transition);" << std::endl;
	stream << "typedef int (*is_matched_t)(const uscxml_ctx* ctx, const uscxml_transition* transition, const void* event);" << std::endl;
	stream << "typedef int (*is_true_t)(const uscxml_ctx* ctx, const char* expr);" << std::endl;
	stream << "typedef int (*exec_content_t)(const uscxml_ctx* ctx, const uscxml_state* state, const void* event);" << std::endl;
	stream << "typedef int (*raise_done_event_t)(const uscxml_ctx* ctx, const uscxml_state* state, const uscxml_elem_donedata* donedata);" << std::endl;
	stream << "typedef int (*invoke_t)(const uscxml_ctx* ctx, const uscxml_state* s, const uscxml_elem_invoke* invocation, unsigned char uninvoke);" << std::endl;
	stream << std::endl;

	stream << "typedef int (*exec_content_log_t)(const uscxml_ctx* ctx, const char* label, const char* expr);" << std::endl;
	stream << "typedef int (*exec_content_raise_t)(const uscxml_ctx* ctx, const char* event);" << std::endl;
	stream << "typedef int (*exec_content_send_t)(const uscxml_ctx* ctx, const uscxml_elem_send* send);" << std::endl;
	stream << "typedef int (*exec_content_foreach_init_t)(const uscxml_ctx* ctx, const uscxml_elem_foreach* foreach);" << std::endl;
	stream << "typedef int (*exec_content_foreach_next_t)(const uscxml_ctx* ctx, const uscxml_elem_foreach* foreach);" << std::endl;
	stream << "typedef int (*exec_content_foreach_done_t)(const uscxml_ctx* ctx, const uscxml_elem_foreach* foreach);" << std::endl;
	stream << "typedef int (*exec_content_assign_t)(const uscxml_ctx* ctx, const uscxml_elem_assign* assign);" << std::endl;
	stream << "typedef int (*exec_content_init_t)(const uscxml_ctx* ctx, const uscxml_elem_data* data);" << std::endl;
	stream << "typedef int (*exec_content_cancel_t)(const uscxml_ctx* ctx, const char* sendid, const char* sendidexpr);" << std::endl;
	stream << "typedef int (*exec_content_finalize_t)(const uscxml_ctx* ctx, const uscxml_elem_invoke* invoker, const void* event);" << std::endl;
	stream << "typedef int (*exec_content_script_t)(const uscxml_ctx* ctx, const char* src, const char* content);" << std::endl;
	stream << std::endl;

	stream << "/**" << std::endl;
	stream << " * A single SCXML state-machine." << std::endl;
	stream << " */" << std::endl;
	stream << "struct uscxml_machine {" << std::endl;
	stream << "    unsigned char               flags;           /* Unused */" << std::endl;
	stream << "    USCXML_NR_STATES_TYPE       nr_states;       /* Make sure to set type per macro! */" << std::endl;
	stream << "    USCXML_NR_TRANS_TYPE        nr_transitions;  /* Make sure to set type per macro! */" << std::endl;
	stream << "    const char*                 name;" << std::endl;
	stream << "    const char*                 datamodel;" << std::endl;
	stream << "    const char*                 uuid;            /* currently MD5 sum */" << std::endl;
	stream << "    const uscxml_state*         states;" << std::endl;
	stream << "    const uscxml_transition*    transitions;" << std::endl;
	stream << "    const uscxml_machine*       parent;" << std::endl;
	stream << "    const uscxml_elem_donedata* donedata;" << std::endl;
	stream << "    const exec_content_t        script;          /* Global script elements */" << std::endl;
	stream << "};" << std::endl;
	stream << std::endl;

	stream << "/**" << std::endl;
	stream << " * All information pertaining to a <data> element->" << std::endl;
	stream << " * With late data binding, blocks of data elements are separated by NULL" << std::endl;
	stream << " * use USCXML_ELEM_DATA_IS_SET to test for end of a block." << std::endl;
	stream << " */" << std::endl;
	stream << "struct uscxml_elem_data {" << std::endl;
	stream << "    const char* id;" << std::endl;
	stream << "    const char* src;" << std::endl;
	stream << "    const char* expr;" << std::endl;
	stream << "    const char* content;" << std::endl;
	stream << "};" << std::endl;
	stream << std::endl;

	stream << "/**" << std::endl;
	stream << " * All information pertaining to an <assign> element->" << std::endl;
	stream << " */" << std::endl;
	stream << "struct uscxml_elem_assign {" << std::endl;
	stream << "    const char* location;" << std::endl;
	stream << "    const char* expr;" << std::endl;
	stream << "    const char* content;" << std::endl;
	stream << "};" << std::endl;
	stream << std::endl;

	stream << "/**" << std::endl;
	stream << " * All information pertaining to any state element->" << std::endl;
	stream << " */" << std::endl;
	stream << "struct uscxml_state {" << std::endl;
	stream << "    const char* name;                                  /* eventual name          */" << std::endl;
	stream << "    const USCXML_NR_STATES_TYPE parent;                /* parent                 */" << std::endl;
	stream << "    const exec_content_t on_entry;                     /* on entry handlers      */" << std::endl;
	stream << "    const exec_content_t on_exit;                      /* on exit handlers       */" << std::endl;
	stream << "    const invoke_t invoke;                             /* invocations            */" << std::endl;
	stream << "    const unsigned char children[USCXML_MAX_NR_STATES_BYTES];   /* all children           */" << std::endl;
	stream << "    const unsigned char completion[USCXML_MAX_NR_STATES_BYTES]; /* default completion     */" << std::endl;
	stream << "    const unsigned char ancestors[USCXML_MAX_NR_STATES_BYTES];  /* all ancestors          */" << std::endl;
	stream << "    const uscxml_elem_data* data;                      /* data with late binding */" << std::endl;
	stream << "    const unsigned char type;                          /* One of USCXML_STATE_*  */" << std::endl;
	stream << "};" << std::endl;
	stream << std::endl;

	stream << "/**" << std::endl;
	stream << " * All information pertaining to a <transitions> element->" << std::endl;
	stream << " */" << std::endl;
	stream << "struct uscxml_transition {" << std::endl;
	stream << "    const USCXML_NR_STATES_TYPE source;" << std::endl;
	stream << "    const unsigned char target[USCXML_MAX_NR_STATES_BYTES];" << std::endl;
	stream << "    const char* event;" << std::endl;
	stream << "    const char* condition;" << std::endl;
	stream << "    const is_enabled_t is_enabled;" << std::endl;
	stream << "    const exec_content_t on_transition;" << std::endl;
	stream << "    const unsigned char type;" << std::endl;
	stream << "    const unsigned char conflicts[USCXML_MAX_NR_TRANS_BYTES];" << std::endl;
	stream << "    const unsigned char exit_set[USCXML_MAX_NR_STATES_BYTES];" << std::endl;
	stream << "};" << std::endl;
	stream << std::endl;

	stream << "/**" << std::endl;
	stream << " * All information pertaining to a <foreach> element->" << std::endl;
	stream << " */" << std::endl;
	stream << "struct uscxml_elem_foreach {" << std::endl;
	stream << "    const char* array;" << std::endl;
	stream << "    const char* item;" << std::endl;
	stream << "    const char* index;" << std::endl;
	stream << "};" << std::endl;
	stream << std::endl;

	stream << "/**" << std::endl;
	stream << " * All information pertaining to a <param> element->" << std::endl;
	stream << " * Blocks of params are separated by NULL params, use" << std::endl;
	stream << " * USCXML_ELEM_PARAM_IS_SET to test for end of a block." << std::endl;
	stream << " */" << std::endl;
	stream << "struct uscxml_elem_param {" << std::endl;
	stream << "    const char* name;" << std::endl;
	stream << "    const char* expr;" << std::endl;
	stream << "    const char* location;" << std::endl;
	stream << "};" << std::endl;
	stream << std::endl;

	stream << "/**" << std::endl;
	stream << " * All information pertaining to a <donedata> element->" << std::endl;
	stream << " */" << std::endl;
	stream << "struct uscxml_elem_donedata {" << std::endl;
	stream << "    const USCXML_NR_STATES_TYPE source;" << std::endl;
	stream << "    const char* content;" << std::endl;
	stream << "    const char* contentexpr;" << std::endl;
	stream << "    const uscxml_elem_param* params;" << std::endl;
	stream << "};" << std::endl;
	stream << std::endl;

	stream << "/**" << std::endl;
	stream << " * All information pertaining to an <invoke> element->" << std::endl;
	stream << " */" << std::endl;
	stream << "struct uscxml_elem_invoke {" << std::endl;
	stream << "    const uscxml_machine* machine;" << std::endl;
	stream << "    const char* type;" << std::endl;
	stream << "    const char* typeexpr;" << std::endl;
	stream << "    const char* src;" << std::endl;
	stream << "    const char* srcexpr;" << std::endl;
	stream << "    const char* id;" << std::endl;
	stream << "    const char* idlocation;" << std::endl;
	stream << "    const char* sourcename;" << std::endl;
	stream << "    const char* namelist;" << std::endl;
	stream << "    const unsigned char autoforward;" << std::endl;
	stream << "    const uscxml_elem_param* params;" << std::endl;
	stream << "    exec_content_finalize_t finalize;" << std::endl;
	stream << "    const char* content;" << std::endl;
	stream << "    const char* contentexpr;" << std::endl;
	stream << "};" << std::endl;
	stream << std::endl;

	stream << "/**" << std::endl;
	stream << " * All information pertaining to a <send> element->" << std::endl;
	stream << " */" << std::endl;
	stream << "struct uscxml_elem_send {" << std::endl;
	stream << "    const char* event;" << std::endl;
	stream << "    const char* eventexpr;" << std::endl;
	stream << "    const char* target;" << std::endl;
	stream << "    const char* targetexpr;" << std::endl;
	stream << "    const char* type;" << std::endl;
	stream << "    const char* typeexpr;" << std::endl;
	stream << "    const char* id;" << std::endl;
	stream << "    const char* idlocation;" << std::endl;
	stream << "    const char* delay;" << std::endl;
	stream << "    const char* delayexpr;" << std::endl;
	stream << "    const char* namelist;    /* not space-separated, still as in attribute value */" << std::endl;
	stream << "    const char* content;" << std::endl;
	stream << "    const char* contentexpr;" << std::endl;
	stream << "    const uscxml_elem_param* params;" << std::endl;
	stream << "};" << std::endl;
	stream << std::endl;

	stream << "/**" << std::endl;
	stream << " * Represents an instance of a state-chart at runtime/" << std::endl;
	stream << " */" << std::endl;
	stream << "struct uscxml_ctx {" << std::endl;
	stream << "    unsigned char         flags;" << std::endl;
	stream << "    const uscxml_machine* machine;" << std::endl;
	stream << std::endl;
	stream << "    unsigned char config[USCXML_MAX_NR_STATES_BYTES]; /* Make sure these macros specify a sufficient size */" << std::endl;
	stream << "    unsigned char history[USCXML_MAX_NR_STATES_BYTES];" << std::endl;
	stream << "    unsigned char invocations[USCXML_MAX_NR_STATES_BYTES];" << std::endl;
	stream << "    unsigned char initialized_data[USCXML_MAX_NR_STATES_BYTES];" << std::endl;
	stream << std::endl;
	stream << "    void* user_data;" << std::endl;
	stream << "    void* event;" << std::endl;
	stream << std::endl;
	stream << "    dequeue_internal_t dequeue_internal;" << std::endl;
	stream << "    dequeue_external_t dequeue_external;" << std::endl;
	stream << "    is_matched_t       is_matched;" << std::endl;
	stream << "    is_true_t          is_true;" << std::endl;
	stream << "    raise_done_event_t raise_done_event;" << std::endl;
	stream << std::endl;
	stream << "    exec_content_log_t          exec_content_log;" << std::endl;
	stream << "    exec_content_raise_t        exec_content_raise;" << std::endl;
	stream << "    exec_content_send_t         exec_content_send;" << std::endl;
	stream << "    exec_content_foreach_init_t exec_content_foreach_init;" << std::endl;
	stream << "    exec_content_foreach_next_t exec_content_foreach_next;" << std::endl;
	stream << "    exec_content_foreach_done_t exec_content_foreach_done;" << std::endl;
	stream << "    exec_content_assign_t       exec_content_assign;" << std::endl;
	stream << "    exec_content_init_t         exec_content_init;" << std::endl;
	stream << "    exec_content_cancel_t       exec_content_cancel;" << std::endl;
	stream << "    exec_content_script_t       exec_content_script;" << std::endl;
	stream << std::endl;
	stream << "    invoke_t invoke;" << std::endl;
	stream << "};" << std::endl;
	stream << std::endl;
	stream << "#define USCXML_NO_GEN_C_TYPES" << std::endl;
	stream << "#endif" << std::endl;
	stream << std::endl;
}

void ChartToC::writeHelpers(std::ostream& stream) {
	stream << "#ifdef USCXML_VERBOSE" << std::endl;
	stream << "/**" << std::endl;
	stream << " * Print name of states contained in a (debugging)." << std::endl;
	stream << " */" << std::endl;
	stream << "static void printStateNames(const uscxml_ctx* ctx, const unsigned char* a, size_t length) {" << std::endl;
	stream << "    size_t i;" << std::endl;
	stream << "    const char* seperator = \"\";" << std::endl;
	stream << "    for (i = 0; i < length; i++) {" << std::endl;
	stream << "        if (BIT_HAS(i, a)) {" << std::endl;
	stream << "            printf(\"%s%s\", seperator, (USCXML_GET_STATE(i).name != NULL ? USCXML_GET_STATE(i).name : \"UNK\"));" << std::endl;
	stream << "            seperator = \", \";" << std::endl;
	stream << "        }" << std::endl;
	stream << "    }" << std::endl;
	stream << "    printf(\"\\n\");" << std::endl;
	stream << "}" << std::endl;
	stream << std::endl;

	stream << "/**" << std::endl;
	stream << " * Print bits set in a in a binary representation (debugging)." << std::endl;
	stream << " */" << std::endl;
	stream << "static void printBitsetIndices(const unsigned char* a, size_t length) {" << std::endl;
	stream << "    size_t i;" << std::endl;
	stream << "    const char* seperator = \"\";" << std::endl;
	stream << "    for (i = 0; i < length; i++) {" << std::endl;
	stream << "        if (BIT_HAS(i, a)) {" << std::endl;
	stream << "            printf(\"%s%zu\", seperator, i);" << std::endl;
	stream << "            seperator = \", \";" << std::endl;
	stream << "        }" << std::endl;
	stream << "    }" << std::endl;
	stream << "    printf(\"\\n\");" << std::endl;
	stream << "}" << std::endl;

	stream << "#endif" << std::endl;
	stream << std::endl;

	stream << "#ifndef USCXML_NO_BIT_OPERATIONS" << std::endl;
	stream << "/**" << std::endl;
	stream << " * Return true if there is a common bit in a and b." << std::endl;
	stream << " */" << std::endl;
	stream << "static int bit_has_and(const unsigned char* a, const unsigned char* b, size_t i) {" << std::endl;
	stream << "    while(i--) {" << std::endl;
	stream << "        if (a[i] & b[i])" << std::endl;
	stream << "            return 1;" << std::endl;
	stream << "    }" << std::endl;
	stream << "    return 0;" << std::endl;
	stream << "}" << std::endl;
	stream << std::endl;

	stream << "/**" << std::endl;
	stream << " * Set all bits to 0, this corresponds to memset(a, 0, i), " << std::endl;
	stream << " * but does not require string.h or cstring." << std::endl;
	stream << " */" << std::endl;
	stream << "static void bit_clear_all(unsigned char* a, size_t i) {" << std::endl;
	stream << "    while(i--) {" << std::endl;
	stream << "        a[i] = 0;" << std::endl;
	stream << "    }" << std::endl;
	stream << "}" << std::endl;
	stream << std::endl;

	stream << "/**" << std::endl;
	stream << " * Return true if there is any bit set in a." << std::endl;
	stream << " */" << std::endl;
	stream << "static int bit_has_any(unsigned const char* a, size_t i) {" << std::endl;
	stream << "    while(i--) {" << std::endl;
	stream << "        if (a[i] > 0)" << std::endl;
	stream << "            return 1;" << std::endl;
	stream << "    }" << std::endl;
	stream << "    return 0;" << std::endl;
	stream << "}" << std::endl;
	stream << std::endl;

	stream << "/**" << std::endl;
	stream << " * Set all bits from given mask in dest, this is |= for bit arrays." << std::endl;
	stream << " */" << std::endl;
	stream << "static void bit_or(unsigned char* dest, const unsigned char* mask, size_t i) {" << std::endl;
	stream << "    while(i--) {" << std::endl;
	stream << "        dest[i] |= mask[i];" << std::endl;
	stream << "    }" << std::endl;
	stream << "}" << std::endl;
	stream << std::endl;

	stream << "/**" << std::endl;
	stream << " * Copy all bits from source to dest, this corresponds to memcpy(a, b, i), " << std::endl;
	stream << " * but does not require string.h or cstring." << std::endl;
	stream << " */" << std::endl;
	stream << "static void bit_copy(unsigned char* dest, const unsigned char* source, size_t i) {" << std::endl;
	stream << "    while(i--) {" << std::endl;
	stream << "        dest[i] = source[i];" << std::endl;
	stream << "    }" << std::endl;
	stream << "}" << std::endl;
	stream << std::endl;

	stream << "/**" << std::endl;
	stream << " * Unset bits from mask in dest." << std::endl;
	stream << " */" << std::endl;
	stream << "static void bit_and_not(unsigned char* dest, const unsigned char* mask, size_t i) {" << std::endl;
	stream << "    while(i--) {" << std::endl;
	stream << "        dest[i] &= ~mask[i];" << std::endl;
	stream << "    }" << std::endl;
	stream << "}" << std::endl;
	stream << std::endl;

	stream << "/**" << std::endl;
	stream << " * Set bits from mask in dest." << std::endl;
	stream << " */" << std::endl;
	stream << "static void bit_and(unsigned char* dest, const unsigned char* mask, size_t i) {" << std::endl;
	stream << "    while(i--) {" << std::endl;
	stream << "        dest[i] &= mask[i];" << std::endl;
	stream << "    };" << std::endl;
	stream << "}" << std::endl;
	stream << std::endl;
	stream << "#define USCXML_NO_BIT_OPERATIONS" << std::endl;
	stream << "#endif" << std::endl;
	stream << std::endl;

}

void ChartToC::writeExecContentFinalize(std::ostream& stream) {

	// needs to be written prior to invocation elem info
	std::list<DOMElement*> finalizes = DOMUtils::inDocumentOrder({ XML_PREFIX(_scxml).str() + "finalize" }, _scxml);

	if (finalizes.size() > 0) {
		stream << "#ifndef USCXML_NO_EXEC_CONTENT" << std::endl;
		stream << std::endl;
	}

	for (auto iter = finalizes.begin(); iter != finalizes.end(); iter++) {
		DOMElement* finalize = *iter;
		std::list<DOMNode*> execContent = DOMUtils::filterChildType(DOMNode::ELEMENT_NODE, finalize);

		if (execContent.size() > 0) {
			stream << "static int " << _prefix << "_" << DOMUtils::idForNode(finalize) << "(const uscxml_ctx* ctx, const uscxml_elem_invoke* invocation, const void* event) {" << std::endl;
			stream << "    int err = USCXML_ERR_OK;" << std::endl;
			for (auto iter2 = execContent.begin(); iter2 != execContent.end(); iter2++) {
				writeExecContent(stream, static_cast<DOMElement*>(*iter2), 1);
			}
			stream << "    return USCXML_ERR_OK;" << std::endl;
			stream << "}" << std::endl;
			stream << std::endl;
		}
	}

	if (finalizes.size() > 0) {
		stream << "#endif" << std::endl;
		stream << std::endl;
	}
}

void ChartToC::writeExecContent(std::ostream& stream) {
	stream << "#ifndef USCXML_NO_EXEC_CONTENT" << std::endl;
	stream << std::endl;

	for (size_t i = 0; i < _states.size(); i++) {
		DOMElement* state(_states[i]);

		if (i == 0) {
			// root state - we need to perform some initialization here
			std::list<DOMElement*> globalScripts = DOMUtils::filterChildElements(XML_PREFIX(state).str() + "script", state);
			if (globalScripts.size() > 0) {
				size_t j = 0;
				for (auto iter = globalScripts.begin(); iter != globalScripts.end(); iter++, j++) {
					DOMElement* globalScript = *iter;

					stream << "static int " << _prefix << "_global_script_" << toStr(j) << "(const uscxml_ctx* ctx, const uscxml_state* state, const void* event) {" << std::endl;
					stream << "    int err = USCXML_ERR_OK;" << std::endl;
					writeExecContent(stream, globalScript, 1);
					stream << "    return USCXML_ERR_OK;" << std::endl;
					stream << "}" << std::endl;
				}

				stream << "static int " << _prefix << "_global_script(const uscxml_ctx* ctx, const uscxml_state* state, const void* event) {" << std::endl;
				for (size_t j = 0; j < globalScripts.size(); j++) {
					stream << "    " << _prefix << "_global_script_" << toStr(j) << "(ctx, state, event);" << std::endl;
				}
				stream << "    return USCXML_ERR_OK;" << std::endl;
				stream << "}" << std::endl;
				stream << std::endl;
			}
		}

		{
			std::list<DOMElement*> onexits = DOMUtils::filterChildElements(XML_PREFIX(state).str() + "onexit", state);
			size_t j = 0;
			for (auto iter = onexits.begin(); iter != onexits.end(); iter++, j++) {
				DOMElement* onexit = *iter;
				stream << "static int " << _prefix << "_" << DOMUtils::idForNode(state) << "_on_exit_" << toStr(j) << "(const uscxml_ctx* ctx, const uscxml_state* state, const void* event) {" << std::endl;
				stream << "    int err = USCXML_ERR_OK;" << std::endl;
				writeExecContent(stream, onexit, 1);
				stream << "    return USCXML_ERR_OK;" << std::endl;
				stream << "}" << std::endl;
				stream << std::endl;
			}

			if (onexits.size() > 0) {
				stream << "static int " << _prefix << "_" << DOMUtils::idForNode(state) << "_on_exit(const uscxml_ctx* ctx, const uscxml_state* state, const void* event) {" << std::endl;
				for (size_t j = 0; j < onexits.size(); j++) {
					stream << "    " << _prefix << "_" << DOMUtils::idForNode(state) << "_on_exit_" << toStr(j) << "(ctx, state, event);" << std::endl;
				}
				stream << "    return USCXML_ERR_OK;" << std::endl;
				stream << "}" << std::endl;
				stream << std::endl;
			}
		}


		{
			std::list<DOMElement*> onentrys = DOMUtils::filterChildElements(XML_PREFIX(state).str() + "onentry", state);
			size_t j = 0;
			for (auto iter = onentrys.begin(); iter != onentrys.end(); iter++, j++) {
				DOMElement* onentry = *iter;
				stream << "static int " << _prefix << "_" << DOMUtils::idForNode(state) << "_on_entry_" << toStr(j) << "(const uscxml_ctx* ctx, const uscxml_state* state, const void* event) {" << std::endl;
				stream << "    int err = USCXML_ERR_OK;" << std::endl;
				writeExecContent(stream, onentry, 1);
				stream << "    return USCXML_ERR_OK;" << std::endl;
				stream << "}" << std::endl;
				stream << std::endl;
			}

			if (onentrys.size() > 0) {
				stream << "static int " << _prefix << "_" << DOMUtils::idForNode(state) << "_on_entry(const uscxml_ctx* ctx, const uscxml_state* state, const void* event) {" << std::endl;
				for (size_t j = 0; j < onentrys.size(); j++) {
					stream << "    " << _prefix << "_" << DOMUtils::idForNode(state) << "_on_entry_" << toStr(j) << "(ctx, state, event);" << std::endl;
				}

				stream << "    return USCXML_ERR_OK;" << std::endl;
				stream << "}" << std::endl;
				stream << std::endl;
			}
		}

		{
			std::list<DOMElement*> invokes = DOMUtils::filterChildElements(XML_PREFIX(state).str() + "invoke", state);
			if (invokes.size() > 0) {
				stream << "static int " << _prefix << "_" << DOMUtils::idForNode(state) << "_invoke(const uscxml_ctx* ctx, const uscxml_state* s, const uscxml_elem_invoke* invocation, unsigned char uninvoke) {" << std::endl;

				size_t j = 0;
				for (auto iter = invokes.begin(); iter != invokes.end(); iter++, j++) {
					DOMElement* invoke = *iter;
					stream << "    ctx->invoke(ctx, s, &" << _prefix << "_elem_invokes[" << ATTR(invoke, "documentOrder") << "], uninvoke);" << std::endl;
					stream << std::endl;
				}
				stream << "    return USCXML_ERR_OK;" << std::endl;
				stream << "}" << std::endl;
			}
		}
	}

	for (size_t i = 0; i < _transitions.size(); i++) {
		DOMElement* transition(_transitions[i]);
		std::list<DOMNode*> execContent = DOMUtils::filterChildType(DOMNode::ELEMENT_NODE, transition);

		if (HAS_ATTR(transition, "cond")) {
			stream << "static int " << _prefix << "_" << DOMUtils::idForNode(transition) << "_is_enabled(const uscxml_ctx* ctx, const uscxml_transition* transition) {" << std::endl;
			if (HAS_ATTR(_scxml, "datamodel") && ATTR(_scxml, "datamodel") == "native") {
				stream << "    return (" << ATTR(transition, "cond") << ");" << std::endl;
			} else {
				stream << "    if likely(ctx->is_true != NULL) {" << std::endl;
				stream << "        return (ctx->is_true(ctx, \"" << escape(ATTR(transition, "cond")) << "\"));" << std::endl;
				stream << "    }" << std::endl;
				stream << "    return USCXML_ERR_MISSING_CALLBACK;" << std::endl;
			}
			stream << "}" << std::endl;
		}

		if (execContent.size() > 0) {
			stream << "static int " << _prefix << "_" << DOMUtils::idForNode(transition) << "_on_trans(const uscxml_ctx* ctx, const uscxml_state* state, const void* event) {" << std::endl;
			stream << "    int err = USCXML_ERR_OK;" << std::endl;
			for (auto iter = execContent.begin(); iter != execContent.end(); iter++) {
				writeExecContent(stream, static_cast<DOMElement*>(*iter), 1);
			}
			stream << "    return USCXML_ERR_OK;" << std::endl;
			stream << "}" << std::endl;
			stream << std::endl;
		}
	}

	stream << "#endif" << std::endl;
	stream << std::endl;

}

void ChartToC::writeExecContent(std::ostream& stream, const DOMNode* node, size_t indent) {
	if (!node)
		return;

	if (node->getNodeType() == DOMNode::TEXT_NODE) {
		if (boost::trim_copy(X(node->getNodeValue()).str()).length() > 0) {
			if (HAS_ATTR(_scxml, "datamodel") && ATTR(_scxml, "datamodel") == "native") {
				stream << node->getNodeValue();
			} else {
				std::string escaped = escape(X(node->getNodeValue()).str());
				stream << escaped;
			}
		}
		return;
	}

	std::string padding;
	for (size_t i = 0; i < indent; i++) {
		padding += "    ";
	}


	if (node->getNodeType() != DOMNode::ELEMENT_NODE)
		return; // skip anything not an element

	DOMElement* elem = (DOMElement*)(node);

	if (false) {
	} else if(TAGNAME(elem) == XML_PREFIX(elem).str() + "onentry" ||
	          TAGNAME(elem) == XML_PREFIX(elem).str() + "onexit" ||
	          TAGNAME(elem) == XML_PREFIX(elem).str() + "transition" ||
	          TAGNAME(elem) == XML_PREFIX(elem).str() + "finalize") {
		// descent into childs and write their contents
		DOMNode* child = node->getFirstChild();
		while(child) {
			writeExecContent(stream, child, indent);
			child = child->getNextSibling();
		}
	} else if(TAGNAME(elem) == XML_PREFIX(elem).str() + "script") {
		stream << padding;
		stream << "if likely(ctx->exec_content_script != NULL) {" << std::endl;
		stream << padding;
		stream << "    if unlikely((err = ctx->exec_content_script(ctx, ";
		stream << (HAS_ATTR(elem, "src") ? "\"" + escape(ATTR(elem, "src")) + "\"" : "NULL") << ", ";

		std::list<DOMNode*> scriptTexts = DOMUtils::filterChildType(DOMNode::TEXT_NODE, elem);
		if (scriptTexts.size() > 0) {
			stream << "\"";
			writeExecContent(stream, scriptTexts.front(), 0);
			stream << "\"";
		} else {
			stream << "NULL";
		}

		stream << ")) != USCXML_ERR_OK) return err;" << std::endl;
		stream << padding << "} else {" << std::endl;
		stream << padding << "    return USCXML_ERR_MISSING_CALLBACK;" << std::endl;
		stream << padding << "}" << std::endl;

	} else if(TAGNAME(elem) == XML_PREFIX(elem).str() + "log") {
		stream << padding;
		stream << "if likely(ctx->exec_content_log != NULL) {" << std::endl;
		stream << padding;
		stream << "    if unlikely((ctx->exec_content_log(ctx, ";
		stream << (HAS_ATTR(elem, "label") ? "\"" + escape(ATTR(elem, "label")) + "\"" : "NULL") << ", ";
		stream << (HAS_ATTR(elem, "expr") ? "\"" + escape(ATTR(elem, "expr")) + "\"" : "NULL");
		stream << ")) != USCXML_ERR_OK) return err;" << std::endl;
		stream << padding << "} else {" << std::endl;
		stream << padding << "    return USCXML_ERR_MISSING_CALLBACK;" << std::endl;
		stream << padding << "}" << std::endl;

	} else if(TAGNAME(elem) == XML_PREFIX(elem).str() + "foreach") {
		stream << padding << "if likely(ctx->exec_content_foreach_init != NULL &&" << std::endl;
		stream << padding << "          ctx->exec_content_foreach_next != NULL &&" << std::endl;
		stream << padding << "          ctx->exec_content_foreach_done != NULL) {" << std::endl;
		stream << std::endl;

		stream << padding << "    if unlikely((ctx->exec_content_foreach_init(ctx, &" << _prefix << "_elem_foreachs[" << ATTR(elem, "documentOrder") << "])) != USCXML_ERR_OK) return err;" << std::endl;
		stream << padding << "    while (ctx->exec_content_foreach_next(ctx, &" << _prefix << "_elem_foreachs[" << ATTR(elem, "documentOrder") << "]) == USCXML_ERR_OK) {" << std::endl;
		DOMNode* child = node->getFirstChild();
		while(child) {
			writeExecContent(stream, child, indent + 2);
			child = child->getNextSibling();
		}
		stream << padding << "    }" << std::endl;
		stream << padding << "    if ((ctx->exec_content_foreach_done(ctx, &" << _prefix << "_elem_foreachs[" << ATTR(elem, "documentOrder") << "])) != USCXML_ERR_OK) return err;" << std::endl;
		stream << padding << "} else {" << std::endl;
		stream << padding << "    return USCXML_ERR_MISSING_CALLBACK;" << std::endl;
		stream << padding << "}" << std::endl;

	} else if(TAGNAME(elem) == XML_PREFIX(elem).str() + "if") {
		stream << padding;
		stream << "if likely(ctx->is_true != NULL) {" << std::endl;
		stream << padding;
		stream << "    if (ctx->is_true(ctx, " << (HAS_ATTR(elem, "cond") ? "\"" + escape(ATTR(elem, "cond")) + "\"" : "NULL") << ")) {" << std::endl;
		DOMNode* child = elem->getFirstChild();
		while(child) {
			if (child->getNodeType() == DOMNode::ELEMENT_NODE && TAGNAME_CAST(child) == "elseif") {
				stream << padding;
				stream << "    } else if (ctx->is_true(ctx, " << (HAS_ATTR_CAST(child, "cond") ? "\"" + escape(ATTR_CAST(child, "cond")) + "\"" : "NULL") << ")) {" << std::endl;
			} else if (child->getNodeType() == DOMNode::ELEMENT_NODE && TAGNAME_CAST(child) == "else") {
				stream << padding;
				stream << "    } else {" << std::endl;
			} else {
				writeExecContent(stream, child, indent + 2);
			}
			child = child->getNextSibling();
		}
		stream << padding << "    }" << std::endl;
		stream << padding << "} else {" << std::endl;
		stream << padding << "    return USCXML_ERR_MISSING_CALLBACK;" << std::endl;
		stream << padding << "}" << std::endl;

	} else if(TAGNAME(elem) == XML_PREFIX(elem).str() + "assign") {
		stream << padding;
		stream << "if likely(ctx->exec_content_assign != NULL) {" << std::endl;
		stream << padding;
		stream << "    if ((ctx->exec_content_assign(ctx, &" << _prefix << "_elem_assigns[" << ATTR(elem, "documentOrder") << "]";
		stream << ")) != USCXML_ERR_OK) return err;" << std::endl;
		stream << padding << "} else {" << std::endl;
		stream << padding << "    return USCXML_ERR_MISSING_CALLBACK;" << std::endl;
		stream << padding << "}" << std::endl;


	} else if(TAGNAME(elem) == XML_PREFIX(elem).str() + "raise") {
		stream << padding;
		stream << "if likely(ctx->exec_content_raise != NULL) {" << std::endl;
		stream << padding;
		stream << "    if unlikely((ctx->exec_content_raise(ctx, ";
		stream << (HAS_ATTR(elem, "event") ? "\"" + escape(ATTR(elem, "event")) + "\"" : "NULL");
		stream << ")) != USCXML_ERR_OK) return err;" << std::endl;
		stream << padding << "} else {" << std::endl;
		stream << padding << "    return USCXML_ERR_MISSING_CALLBACK;" << std::endl;
		stream << padding << "}" << std::endl;

	} else if(TAGNAME(elem) == XML_PREFIX(elem).str() + "send") {
		stream << padding;
		stream << "if likely(ctx->exec_content_send != NULL) {" << std::endl;
		stream << padding;
		stream << "    if ((ctx->exec_content_send(ctx, &" << _prefix << "_elem_sends[" << ATTR(elem, "documentOrder") << "]";
		stream << ")) != USCXML_ERR_OK) return err;" << std::endl;
		stream << padding << "} else {" << std::endl;
		stream << padding << "    return USCXML_ERR_MISSING_CALLBACK;" << std::endl;
		stream << padding << "}" << std::endl;

	} else if(TAGNAME(elem) == XML_PREFIX(elem).str() + "cancel") {
		stream << padding;
		stream << "if likely(ctx->exec_content_cancel != NULL) {" << std::endl;
		stream << padding;
		stream << "    if ((ctx->exec_content_cancel(ctx, ";
		stream << (HAS_ATTR(elem, "sendid") ? "\"" + escape(ATTR(elem, "sendid")) + "\"" : "NULL") << ", ";
		stream << (HAS_ATTR(elem, "sendidexpr") ? "\"" + escape(ATTR(elem, "sendidexpr")) + "\"" : "NULL");
		stream << ")) != USCXML_ERR_OK) return err;" << std::endl;
		stream << padding << "} else {" << std::endl;
		stream << padding << "    return USCXML_ERR_MISSING_CALLBACK;" << std::endl;
		stream << padding << "}" << std::endl;

	} else {
		std::cerr << "'" << TAGNAME(elem) << "'" << std::endl << elem << std::endl;
		assert(false);
	}

}

void ChartToC::writeElementInfoInvocation(std::ostream& stream) {

	stream << "#ifndef USCXML_NO_ELEM_INFO" << std::endl;
	stream << std::endl;

	std::list<DOMElement*> invokes = DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "invoke", _scxml, true);
	if (invokes.size() > 0) {
		_hasElement.insert("invoke");
		stream << "static const uscxml_elem_invoke " << _prefix << "_elem_invokes[" << invokes.size() << "] = {" << std::endl;
		size_t i = 0;
		for (auto iter = invokes.begin(); iter != invokes.end(); iter++, i++) {
			DOMElement* invoke = *iter;

			/*
			 stream << "struct uscxml_elem_invoke {" << std::endl;
			 stream << "    const char* machine;" << std::endl;
			 stream << "    const char* type;" << std::endl;
			 stream << "    const char* typeexpr;" << std::endl;
			 stream << "    const char* src;" << std::endl;
			 stream << "    const char* srcexpr;" << std::endl;
			 stream << "    const char* id;" << std::endl;
			 stream << "    const char* idlocation;" << std::endl;
			 stream << "    const char* sourcename;" << std::endl;
			 stream << "    const char* namelist;" << std::endl;
			 stream << "    const unsigned char autoforward;" << std::endl;
			 stream << "    const uscxml_elem_param* params;" << std::endl;
			 stream << "    const exec_content_finalize_t* finalize;" << std::endl;
			 stream << "    const char* content;" << std::endl;
			 stream << "    const char* contentexpr;" << std::endl;
			 stream << "};" << std::endl;
			 */

			stream << "    { " << std::endl;

			stream << "        /* machine     */ ";
			if (HAS_ATTR(invoke, "md5sum")) {
#if 1
				size_t machIdx = 0;
				for (std::list<ChartToC*>::iterator machIter = _allMachines.begin(); machIter != _allMachines.end(); machIter++, machIdx++) {
					if ((*machIter)->_md5 == ATTR(invoke, "md5sum")) {
						stream << "&" << (*machIter)->_prefix << "_machine";
						break;
					}
				}
#else
				size_t machIdx = 0;
				for (std::list<ChartToC*>::iterator machIter = _allMachines.begin(); machIter != _allMachines.end(); machIter++, machIdx++) {
					if ((*machIter)->_md5 == ATTR(invoke, "md5sum")) {
						stream << "&uscxml_machines[" << toStr(machIdx) << "]";
						break;
					}
				}
#endif
			} else {
				stream << "NULL";
			}
			stream << ", " << std::endl;

			stream << "        /* type        */ ";
			stream << (HAS_ATTR(invoke, "type") ? "\"" +  escape(ATTR(invoke, "type")) + "\"" : "NULL");
			stream << ", " << std::endl;

			stream << "        /* typeexpr    */ ";
			stream << (HAS_ATTR(invoke, "typeexpr") ? "\"" +  escape(ATTR(invoke, "typeexpr")) + "\"" : "NULL");
			stream << ", " << std::endl;

			stream << "        /* src         */ ";
			stream << (HAS_ATTR(invoke, "src") ? "\"" + escape(ATTR(invoke, "src")) + "\"" : "NULL");
			stream << ", " << std::endl;

			stream << "        /* srcexpr     */ ";
			stream << (HAS_ATTR(invoke, "srcexpr") ? "\"" +  escape(ATTR(invoke, "srcexpr")) + "\"" : "NULL");
			stream << ", " << std::endl;

			stream << "        /* id          */ ";
			stream << (HAS_ATTR(invoke, "id") ? "\"" +  escape(ATTR(invoke, "id")) + "\"" : "NULL");
			stream << ", " << std::endl;

			stream << "        /* idlocation  */ ";
			stream << (HAS_ATTR(invoke, "idlocation") ? "\"" +  escape(ATTR(invoke, "idlocation")) + "\"" : "NULL");
			stream << ", " << std::endl;

			stream << "        /* sourcename  */ ";
			stream << (HAS_ATTR_CAST(invoke->getParentNode(), "id") ? "\"" +  escape(ATTR_CAST(invoke->getParentNode(), "id")) + "\"" : "NULL");
			stream << ", " << std::endl;

			stream << "        /* namelist    */ ";
			stream << (HAS_ATTR(invoke, "namelist") ? "\"" +  escape(ATTR(invoke, "namelist")) + "\"" : "NULL");
			stream << ", " << std::endl;

			stream << "        /* autoforward */ ";
			stream << (HAS_ATTR(invoke, "autoforward") && stringIsTrue(ATTR(invoke, "autoforward")) ? "1" : "0");
			stream << ", " << std::endl;

			stream << "        /* params      */ ";
			if (HAS_ATTR(invoke, "paramIndex")) {
				stream << "&" << _prefix << "_elem_params[" << escape(ATTR(invoke, "paramIndex")) << "]";
			} else {
				stream << "NULL";
			}
			stream << ", " << std::endl;

			stream << "        /* finalize    */ ";
			std::list<DOMElement*> finalizes = DOMUtils::filterChildElements(XML_PREFIX(invoke).str() + "finalize", invoke);
			if (finalizes.size() > 0) {
				stream << _prefix << "_" << DOMUtils::idForNode(finalizes.front());
			} else {
				stream << "NULL";
			}
			stream << ", " << std::endl;

			std::list<DOMElement*> contents = DOMUtils::filterChildElements(XML_PREFIX(invoke).str() + "content", invoke);
			if (contents.size() > 0 && !HAS_ATTR(invoke, "md5sum")) {
				std::stringstream ss;
				DOMNodeList* cChilds = contents.front()->getChildNodes();
				for (size_t j = 0; j < cChilds->getLength(); j++) {
					ss << cChilds->item(j);
				}
				stream << "        /* content      */ ";
				stream << (ss.str().size() > 0 ? "\"" + escape(ss.str()) + "\", " : "NULL, ") << std::endl;
				stream << "        /* contentexpr  */ ";
				stream << (HAS_ATTR_CAST(contents.front(), "expr") ? "\"" + ATTR_CAST(contents.front(), "expr") + "\", " : "NULL, ") << std::endl;
			} else {
				stream << "        /* content     */ NULL," << std::endl;
				stream << "        /* contentexpr */ NULL," << std::endl;
			}

			stream << "    }" << (i + 1 < invokes.size() ? ",": "") << std::endl;
			invoke->setAttribute(X("documentOrder"), X(toStr(i)));

		}
		stream << "};" << std::endl;
		stream << std::endl;
	}

	stream << "#endif" << std::endl;
	stream << std::endl;

}

void ChartToC::writeElementInfo(std::ostream& stream) {
	stream << "#ifndef USCXML_NO_ELEM_INFO" << std::endl;
	stream << std::endl;

	std::list<DOMElement*> foreachs = DOMUtils::inDocumentOrder({ XML_PREFIX(_scxml).str() + "foreach" }, _scxml);
	if (foreachs.size() > 0) {
		_hasElement.insert("foreach");
		stream << "static const uscxml_elem_foreach " << _prefix << "_elem_foreachs[" << foreachs.size() << "] = {" << std::endl;
		stream << "    /* array, item, index */" << std::endl;
		size_t i = 0;
		for (auto iter = foreachs.begin(); iter != foreachs.end(); iter++, i++) {
			DOMElement* foreach = *iter;
			stream << "    { ";
			stream << (HAS_ATTR(foreach, "array") ? "\"" + escape(ATTR(foreach, "array")) + "\"" : "NULL") << ", ";
			stream << (HAS_ATTR(foreach, "item") ? "\"" + escape(ATTR(foreach, "item")) + "\"" : "NULL") << ", ";
			stream << (HAS_ATTR(foreach, "index") ? "\"" + escape(ATTR(foreach, "index")) + "\"" : "NULL");
			stream << " }" << (i + 1 < foreachs.size() ? ",": "") << std::endl;
			foreach->setAttribute(X("documentOrder"), X(toStr(i)));
		}
		stream << "};" << std::endl;
		stream << std::endl;
	}

	std::list<DOMElement*> assigns = DOMUtils::inDocumentOrder({ XML_PREFIX(_scxml).str() + "assign" }, _scxml);
	if (assigns.size() > 0) {
		_hasElement.insert("assign");
		stream << "static const uscxml_elem_assign " << _prefix << "_elem_assigns[" << assigns.size() << "] = {" << std::endl;
		stream << "    /* location, expr, content */" << std::endl;

		size_t i = 0;
		for (auto iter = assigns.begin(); iter != assigns.end(); iter++, i++) {
			DOMElement* assign = *iter;

			stream << "    { ";
			stream << (HAS_ATTR(assign, "location") ? "\"" + escape(ATTR(assign, "location")) + "\"" : "NULL") << ", ";
			stream << (HAS_ATTR(assign, "expr") ? "\"" + escape(ATTR(assign, "expr")) + "\"" : "NULL") << ", ";

			std::list<DOMNode*> assignTexts = DOMUtils::filterChildType(DOMNode::TEXT_NODE, assign);
			if (assignTexts.size() > 0) {
				if (boost::trim_copy(X(assignTexts.front()->getNodeValue()).str()).length() > 0) {
					std::string escaped = escape(X(assignTexts.front()->getNodeValue()).str());
					stream << "\"" << escaped << "\"";
				}
			} else {
				stream << "NULL";
			}
			stream << " }," << std::endl;

			assign->setAttribute(X("documentOrder"), X(toStr(i)));
		}

		stream << "};" << std::endl;
		stream << std::endl;

	}

	std::list<DOMElement*> datas = DOMUtils::inDocumentOrder({ XML_PREFIX(_scxml).str() + "data" }, _scxml);
	if (datas.size() > 0) {
		_hasElement.insert("data");
		size_t dataIndexOffset = 0;
		DOMNode* parent = NULL;
		size_t distinctParents = 0;

		if (_binding == InterpreterImpl::EARLY) {
			_states[0]->setAttribute(X("dataIndex"), X("0"));
			distinctParents = 1;
		} else {
			for (auto iter = datas.begin(); iter != datas.end(); iter++) {
				DOMElement* data = *iter;
				if (data->getParentNode() != parent) {
					distinctParents++;
				}
			}
		}

		parent = NULL;

		stream << "static const uscxml_elem_data " << _prefix << "_elem_datas[" << datas.size() + distinctParents << "] = {" << std::endl;
		stream << "    /* id, src, expr, content */" << std::endl;
		size_t i = 0;
		for (auto iter = datas.begin(); iter != datas.end(); iter++, i++) {
			DOMElement* data = *iter;
			if (data->getParentNode()->getParentNode() != parent) {
				if (_binding == InterpreterImpl::LATE) {
					if (i > 0) {
						stream << "    { NULL, NULL, NULL, NULL }," << std::endl;
						dataIndexOffset++;
					}
					static_cast<DOMElement*>(data->getParentNode()->getParentNode())->setAttribute(X("dataIndex"), X(toStr(i + dataIndexOffset)));
				}
				parent = data->getParentNode()->getParentNode();
			}
			stream << "    { ";
			stream << (HAS_ATTR(data, "id") ? "\"" + escape(ATTR(data, "id")) + "\"" : "NULL") << ", ";
			stream << (HAS_ATTR(data, "src") ? "\"" + escape(ATTR(data, "src")) + "\"" : "NULL") << ", ";
			stream << (HAS_ATTR(data, "expr") ? "\"" + escape(ATTR(data, "expr")) + "\"" : "NULL") << ", ";

			std::list<DOMNode*> dataTexts = DOMUtils::filterChildType(DOMNode::TEXT_NODE, data);
			if (dataTexts.size() > 0) {
				if (boost::trim_copy(X(dataTexts.front()->getNodeValue()).str()).length() > 0) {
					std::string escaped = escape(X(dataTexts.front()->getNodeValue()).str());
					stream << "\"" << escaped << "\"";
				}
			} else {
				stream << "NULL";
			}
			stream << " }," << std::endl;

		}
		stream << "    { NULL, NULL, NULL, NULL }" << std::endl;
		stream << "};" << std::endl;
		stream << std::endl;
	}

	std::list<DOMElement*> params = DOMUtils::inDocumentOrder({ XML_PREFIX(_scxml).str() + "param" }, _scxml);
	if (params.size() > 0) {
		_hasElement.insert("param");
		DOMNode* parent = NULL;
		size_t distinctParents = 0;
		for (auto iter = params.begin(); iter != params.end(); iter++) {
			DOMElement* param = *iter;
			if (param->getParentNode() != parent) {
				distinctParents++;
			}
		}
		parent = NULL;

		stream << "static const uscxml_elem_param " << _prefix << "_elem_params[" << params.size() + distinctParents << "] = {" << std::endl;
		stream << "    /* name, expr, location */" << std::endl;
		size_t i = 0;
		for (auto iter = params.begin(); iter != params.end(); iter++, i++) {
			DOMElement* param = *iter;
			if (param->getParentNode() != parent) {
				static_cast<DOMElement*>(param->getParentNode())->setAttribute(X("paramIndex"), X(toStr(i)));
				if (i > 0) {
					stream << "    { NULL, NULL, NULL }," << std::endl;
				}
				parent = param->getParentNode();
			}
			stream << "    { ";
			stream << (HAS_ATTR(param, "name") ? "\"" + escape(ATTR(param, "name")) + "\"" : "NULL") << ", ";
			stream << (HAS_ATTR(param, "expr") ? "\"" + escape(ATTR(param, "expr")) + "\"" : "NULL") << ", ";
			stream << (HAS_ATTR(param, "location") ? "\"" + escape(ATTR(param, "location")) + "\"" : "NULL");
			stream << " }," << std::endl;

		}
		stream << "    { NULL, NULL, NULL }" << std::endl;
		stream << "};" << std::endl;
		stream << std::endl;
	}

	std::list<DOMElement*> sends = DOMUtils::inDocumentOrder({ XML_PREFIX(_scxml).str() + "send" }, _scxml);
	if (sends.size() > 0) {
		_hasElement.insert("send");
		stream << "static const uscxml_elem_send " << _prefix << "_elem_sends[" << sends.size() << "] = {" << std::endl;
		size_t i = 0;
		for (auto iter = sends.begin(); iter != sends.end(); iter++, i++) {
			DOMElement* send = *iter;
			stream << "    { ";
			stream << std::endl << "        /* event       */ ";
			stream << (HAS_ATTR(send, "event") ? "\"" + escape(ATTR(send, "event")) + "\"" : "NULL") << ", ";
			stream << std::endl << "        /* eventexpr   */ ";
			stream << (HAS_ATTR(send, "eventexpr") ? "\"" + escape(ATTR(send, "eventexpr")) + "\"" : "NULL") << ", ";
			stream << std::endl << "        /* target      */ ";
			stream << (HAS_ATTR(send, "target") ? "\"" + escape(ATTR(send, "target")) + "\"" : "NULL") << ", ";
			stream << std::endl << "        /* targetexpr  */ ";
			stream << (HAS_ATTR(send, "targetexpr") ? "\"" + escape(ATTR(send, "targetexpr")) + "\"" : "NULL") << ", ";
			stream << std::endl << "        /* type        */ ";
			stream << (HAS_ATTR(send, "type") ? "\"" + escape(ATTR(send, "type")) + "\"" : "NULL") << ", ";
			stream << std::endl << "        /* typeexpr    */ ";
			stream << (HAS_ATTR(send, "typeexpr") ? "\"" + escape(ATTR(send, "typeexpr")) + "\"" : "NULL") << ", ";
			stream << std::endl << "        /* id          */ ";
			stream << (HAS_ATTR(send, "id") ? "\"" + escape(ATTR(send, "id")) + "\"" : "NULL") << ", ";
			stream << std::endl << "        /* idlocation  */ ";
			stream << (HAS_ATTR(send, "idlocation") ? "\"" + escape(ATTR(send, "idlocation")) + "\"" : "NULL") << ", ";
			stream << std::endl << "        /* delay       */ ";
			stream << (HAS_ATTR(send, "delay") ? "\"" + escape(ATTR(send, "delay")) + "\"" : "NULL") << ", ";
			stream << std::endl << "        /* delayexpr   */ ";
			stream << (HAS_ATTR(send, "delayexpr") ? "\"" + escape(ATTR(send, "delayexpr")) + "\"" : "NULL") << ", ";
			stream << std::endl << "        /* namelist    */ ";
			stream << (HAS_ATTR(send, "namelist") ? "\"" + escape(ATTR(send, "namelist")) + "\"" : "NULL") << ", ";

			std::list<DOMElement*> contents = DOMUtils::filterChildElements(XML_PREFIX(send).str() + "content", send);
			if (contents.size() > 0) {
				std::stringstream ss;
				DOMNodeList* cChilds = contents.front()->getChildNodes();
				for (size_t j = 0; j < cChilds->getLength(); j++) {
					ss << *(cChilds->item(j));
				}
				stream << std::endl << "        /* content     */ ";
				stream << (ss.str().size() > 0 ? "\"" + escape(ss.str()) + "\", " : "NULL, ");
				stream << std::endl << "        /* contentexpr  */ ";
				stream << (HAS_ATTR_CAST(contents.front(), "expr") ? "\"" + ATTR_CAST(contents.front(), "expr") + "\", " : "NULL, ");
			} else {
				stream << std::endl << "        /* content     */ ";
				stream << "NULL,";
				stream << std::endl << "        /* contentexpr */ ";
				stream << "NULL,";
			}


			stream << std::endl << "        /* params      */ ";
			if (HAS_ATTR(send, "paramIndex")) {
				stream << "&" << _prefix << "_elem_params[" << escape(ATTR(send, "paramIndex")) << "] ";
			} else {
				stream << "NULL ";
			}

			stream << std::endl << "    }" << (i + 1 < sends.size() ? ",": "") << std::endl;
			send->setAttribute(X("documentOrder"), X(toStr(i)));
		}
		stream << "};" << std::endl;
		stream << std::endl;
	}

	std::list<DOMElement*> donedatas = DOMUtils::inDocumentOrder({ XML_PREFIX(_scxml).str() + "donedata" }, _scxml);
	stream << "static const uscxml_elem_donedata " << _prefix << "_elem_donedatas[" << donedatas.size() + 1 << "] = {" << std::endl;
	stream << "    /* source, content, contentexpr, params */" << std::endl;
	size_t i = 0;
	for (auto iter = donedatas.begin(); iter != donedatas.end(); iter++, i++) {
		DOMElement* donedata = *iter;

		_hasElement.insert("donedata");
		stream << "    { ";

		// parent
		stream << ATTR_CAST(donedata->getParentNode(), "documentOrder") << ", ";

		std::list<DOMElement*> contents = DOMUtils::filterChildElements(XML_PREFIX(donedata).str() + "content", donedata);
		if (contents.size() > 0) {
			std::stringstream ss;
			DOMNodeList* cChilds = contents.front()->getChildNodes();
			for (size_t j = 0; j < cChilds->getLength(); j++) {
				ss << *(cChilds->item(j));
			}
			stream << (ss.str().size() > 0 ? "\"" + escape(ss.str()) + "\", " : "NULL, ");
			stream << (HAS_ATTR_CAST(contents.front(), "expr") ? "\"" + ATTR_CAST(contents.front(), "expr") + "\", " : "NULL, ");
		} else {
			stream << "NULL, NULL, ";
		}

		if (HAS_ATTR(donedata, "paramIndex")) {
			stream << "&" << _prefix << "_elem_params[" << escape(ATTR(donedata, "paramIndex")) << "]";
		} else {
			stream << "NULL";
		}

		stream << " }," << std::endl;
		donedata->setAttribute(X("documentOrder"), X(toStr(i)));
	}
	stream << "    { 0, NULL, NULL, NULL }" << std::endl;
	stream << "};" << std::endl;
	stream << std::endl;

	stream << "#endif" << std::endl;
	stream << std::endl;

}

void ChartToC::writeMachineInfo(std::ostream& stream) {

	stream << "#ifndef USCXML_NO_ELEM_INFO" << std::endl;
	stream << std::endl;

#if 1
	size_t currIndex = 0;
	char* currIndexStr = getenv("USCXML_CURRENT_MACHINE_INDEX");
	if (currIndexStr != NULL) {
		currIndex = strTo<size_t>(currIndexStr);
	}

	stream << "#ifndef USCXML_MACHINE" << std::endl;
	stream << "#  define USCXML_MACHINE " << _prefix << "_machine" << std::endl;
	stream << "#endif" << std::endl;

	stream << "#define USCXML_MACHINE_" << toStr(currIndex) << " " << _prefix << "_machine" << std::endl;

	if (_name.size() > 0) {
		std::string macroName = boost::to_upper_copy(escape(_name));
		boost::replace_all(macroName, "-", "_");
		boost::replace_all(macroName, ".", "_");
		stream << "#define USCXML_MACHINE_" << macroName << " " << _prefix << "_machine" << std::endl;
	}
	stream << std::endl;

	currIndex++;
	setenv("USCXML_CURRENT_MACHINE_INDEX", toStr(currIndex).c_str(), 1);

	stream << "const uscxml_machine " << _prefix << "_machine = {" << std::endl;
	stream << "        /* flags          */ 0," << std::endl;
	stream << "        /* nr_states      */ " << _states.size() << "," << std::endl;
	stream << "        /* nr_transitions */ " << _transitions.size() << "," << std::endl;
	stream << "        /* name           */ \"" << escape(_name) << "\"," << std::endl;
	stream << "        /* datamodel      */ \"" << (HAS_ATTR(_scxml, "datamodel") ? ATTR(_scxml, "datamodel") : "null") << "\"," << std::endl;
	stream << "        /* uuid           */ \"" << _md5 << "\"," << std::endl;
	stream << "        /* states         */ " << "&" << _prefix << "_states[0], " << std::endl;
	if (_transitions.size() > 0) {
		stream << "        /* transitions    */ " << "&" << _prefix << "_transitions[0], " << std::endl;
	} else {
		stream << "        /* transitions    */ " << "NULL, " << std::endl;
	}
	stream << "        /* parent         */ ";
	if (_parentMachine != NULL) {
		size_t parentIndex = 0;
		for (std::list<ChartToC*>::iterator parentIter = _topMostMachine->_allMachines.begin();
		        parentIter != _topMostMachine->_allMachines.end();
		        parentIter++, parentIndex++) {
			if (*parentIter == _parentMachine) {
				stream << "&" << (*parentIter)->_prefix << "_machine";
			}
		}
	} else {
		stream << "NULL";
	}
	stream << "," << std::endl;

	stream << "        /* donedata       */ " << "&" << _prefix << "_elem_donedatas[0], " << std::endl;
	stream << "        /* script         */ ";
	if (DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "script", _scxml).size() > 0) {
		stream << _prefix << "_global_script" << std::endl;
	} else {
		stream << "NULL";
	}
	stream << std::endl;

	stream << "};" << std::endl;
	stream << std::endl;

#else
	if (_topMostMachine != NULL)
		return;

	stream << "const uscxml_machine uscxml_machines[" << _allMachines.size() + 1<< "] = {" << std::endl;
	for (std::list<ChartToC*>::iterator machineIter = _allMachines.begin(); machineIter != _allMachines.end(); machineIter++) {
		ChartToC* m = (*machineIter);
		stream << "    {" << std::endl;
		stream << "        /* flags          */ 0," << std::endl;
		stream << "        /* nr_states      */ " << m->_states.size() << "," << std::endl;
		stream << "        /* nr_transitions */ " << m->_transitions.size() << "," << std::endl;
		stream << "        /* name           */ \"" << escape(m->_name) << "\"," << std::endl;
		stream << "        /* datamodel      */ \"" << (HAS_ATTR(m->_scxml, "datamodel") ? ATTR(m->_scxml, "datamodel") : "null") << "\"," << std::endl;
		stream << "        /* uuid           */ \"" << m->_md5 << "\"," << std::endl;
		stream << "        /* states         */ " << "&" << m->_prefix << "_states[0], " << std::endl;
		stream << "        /* transitions    */ " << "&" << m->_prefix << "_transitions[0], " << std::endl;
		stream << "        /* parent         */ ";
		if (m->_parentMachine != NULL) {
			size_t parentIndex = 0;
			for (std::list<ChartToC*>::iterator parentIter = _allMachines.begin(); parentIter != _allMachines.end(); parentIter++, parentIndex++) {
				if (*parentIter == m->_parentMachine) {
					stream << "&uscxml_machines[" << toStr(parentIndex) << "]";
				}
			}
		} else {
			stream << "NULL";
		}
		stream << "," << std::endl;

		stream << "        /* donedata       */ " << "&" << m->_prefix << "_elem_donedatas[0], " << std::endl;
		stream << "        /* script         */ ";
		if (DOMUtils::filterChildElements(XML_PREFIX(node).str() + "script", _scxml).size() > 0) {
			stream << m->_prefix << "_global_script" << std::endl;
		} else {
			stream << "NULL";
		}
		stream << std::endl;

		stream << "    }," << std::endl;

	}
	stream << "    {0, 0, 0, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL }" << std::endl;
	stream << "};" << std::endl;
	stream << std::endl;
#endif

	stream << "#endif" << std::endl;
	stream << std::endl;

}

void ChartToC::writeStates(std::ostream& stream) {
	stream << "#ifndef USCXML_NO_ELEM_INFO" << std::endl;
	stream << std::endl;

	stream << "static const uscxml_state " << _prefix << "_states[" << toStr(_states.size()) << "] = {" << std::endl;
	for (size_t i = 0; i < _states.size(); i++) {
		DOMElement* state(_states[i]);

		stream << "    {   /* state number " << toStr(i) << " */" << std::endl;

		// name
		stream << "        /* name       */ ";
		stream << (HAS_ATTR(state, "id") ? "\"" + escape(ATTR(state, "id")) + "\"" : "NULL");
		stream << "," << std::endl;

		// parent
		stream << "        /* parent     */ ";
		stream << (i == 0 ? "0" : ATTR_CAST(state->getParentNode(), "documentOrder"));
		stream << "," << std::endl;

		// onentry
		stream << "        /* onentry    */ ";
		stream << (DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "onentry", state).size() > 0 ? _prefix + "_" + DOMUtils::idForNode(state) + "_on_entry" : "NULL");
		stream << "," << std::endl;

		// onexit
		stream << "        /* onexit     */ ";
		stream << (DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "onexit", state).size() > 0 ? _prefix + "_" + DOMUtils::idForNode(state) + "_on_exit" : "NULL");
		stream << "," << std::endl;

		// invokers
		stream << "        /* invoke     */ ";
		stream << (DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "invoke", state).size() > 0 ? _prefix + "_" + DOMUtils::idForNode(state) + "_invoke" : "NULL");
		stream << "," << std::endl;

		// children
		stream << "        /* children   */ { ";
		writeCharArrayInitList(stream, ATTR(state, "childBools"));
		stream << " /* " << ATTR(state, "childBools") << " */ }," << std::endl;

		// default completion
		stream << "        /* completion */ { ";
		writeCharArrayInitList(stream, ATTR(state, "completionBools"));
		stream << " /* " << ATTR(state, "completionBools") << " */ }, \t" << std::endl;

		stream << "        /* ancestors  */ { ";
		writeCharArrayInitList(stream, ATTR(state, "ancBools"));
		stream << " /* " << ATTR(state, "ancBools") << " */ }," << std::endl;

		stream << "        /* data       */ ";
		stream << (HAS_ATTR(state, "dataIndex") ? "&" + _prefix + "_elem_datas[" + escape(ATTR(state, "dataIndex")) + "]" : "NULL");
		stream << "," << std::endl;

		stream << "        /* type       */ ";

		if (false) {
		} else if (iequals(TAGNAME(state), "initial")) {
			stream << "USCXML_STATE_INITIAL";
		} else if (isFinal(state)) {
			stream << "USCXML_STATE_FINAL";
		} else if (isHistory(state)) {
			if (HAS_ATTR(state, "type") && iequals(ATTR(state, "type"), "deep")) {
				stream << "USCXML_STATE_HISTORY_DEEP";
			} else {
				stream << "USCXML_STATE_HISTORY_SHALLOW";
			}
		} else if (isAtomic(state)) {
			stream << "USCXML_STATE_ATOMIC";
		} else if (isParallel(state)) {
			stream << "USCXML_STATE_PARALLEL";
		} else if (isCompound(state)) {
			stream << "USCXML_STATE_COMPOUND";
		} else { // <scxml>
			stream << "USCXML_STATE_COMPOUND";
		}
		if (HAS_ATTR(state, "hasHistoryChild")) {
			stream << " | USCXML_STATE_HAS_HISTORY";
		}

		stream << "," << std::endl;

		stream << "    }" << (i + 1 < _states.size() ? ",": "") << std::endl;
	}
	stream << "};" << std::endl;
	stream << std::endl;

	stream << "#endif" << std::endl;
	stream << std::endl;

}


void ChartToC::writeTransitions(std::ostream& stream) {

	stream << "#ifndef USCXML_NO_ELEM_INFO" << std::endl;
	stream << std::endl;

	// cross reference transition by document order - is this really needed?!
	std::list<DOMElement*> transDocOrder = DOMUtils::inDocumentOrder({ XML_PREFIX(_scxml).str() + "transition" }, _scxml);

	if (_transitions.size() > 0) {
		stream << "static const uscxml_transition " << _prefix << "_transitions[" << toStr(_transitions.size()) << "] = {" << std::endl;
		for (size_t i = 0; i < _transitions.size(); i++) {
			DOMElement* transition(_transitions[i]);

			stream << "    {   /* transition number " << ATTR(transition, "documentOrder") << " with priority " << toStr(i) << std::endl;
			stream << "           target: " << ATTR(transition, "target") << std::endl;
			stream << "         */" << std::endl;

			// source
			stream << "        /* source     */ ";
			stream << ATTR_CAST(transition->getParentNode(), "documentOrder");
			stream << "," << std::endl;

			// targets
			stream << "        /* target     */ ";
			if (HAS_ATTR(transition, "targetBools")) {
				stream << "{ ";
				writeCharArrayInitList(stream, ATTR(transition, "targetBools"));
				stream << " /* " << ATTR(transition, "targetBools") << " */ }";

			} else {
				stream << "{ 0x00 }";
			}
			stream << "," << std::endl;

			stream << "        /* event      */ ";
			stream << (HAS_ATTR(transition, "event") ? "\"" + escape(ATTR(transition, "event")) + "\"" : "NULL");
			stream << "," << std::endl;

			stream << "        /* condition  */ ";
			stream << (HAS_ATTR(transition, "cond") ? "\"" + escape(ATTR(transition, "cond")) + "\"" : "NULL");
			stream << "," << std::endl;


			// is enabled
			stream << "        /* is_enabled */ ";
			if (HAS_ATTR(transition, "cond")) {
				stream << _prefix << "_" << DOMUtils::idForNode(transition) << "_is_enabled";
			} else {
				stream << "NULL";
			}
			stream << "," << std::endl;

			// on transition handlers
			stream << "        /* ontrans    */ ";
			if (DOMUtils::filterChildType(DOMNode::ELEMENT_NODE, transition).size() > 0) {
				stream << _prefix << "_" << DOMUtils::idForNode(transition) + "_on_trans";
			} else {
				stream << "NULL";
			}
			stream << "," << std::endl;

			// type
			stream << "        /* type       */ ";
			std::string seperator = "";
			if (!HAS_ATTR(transition, "target")) {
				stream << seperator << "USCXML_TRANS_TARGETLESS";
				seperator = " | ";
			}

			if (HAS_ATTR(transition, "type") && iequals(ATTR(transition, "type"), "internal")) {
				stream << seperator << "USCXML_TRANS_INTERNAL";
				seperator = " | ";
			}

			if (!HAS_ATTR(transition, "event")) {
				stream << seperator << "USCXML_TRANS_SPONTANEOUS";
				seperator = " | ";
			}

			if (iequals(TAGNAME_CAST(transition->getParentNode()), "history")) {
				stream << seperator << "USCXML_TRANS_HISTORY";
				seperator = " | ";
			}

			if (iequals(TAGNAME_CAST(transition->getParentNode()), "initial")) {
				stream << seperator << "USCXML_TRANS_INITIAL";
				seperator = " | ";
			}

			if (seperator.size() == 0) {
				stream << "0";
			}
			stream << "," << std::endl;

			// conflicts
			stream << "        /* conflicts  */ { ";
			writeCharArrayInitList(stream, ATTR(transition, "conflictBools"));
			stream << " /* " << ATTR(transition, "conflictBools") << " */ }, " << std::endl;

			// exit set
			stream << "        /* exit set   */ { ";
			writeCharArrayInitList(stream, ATTR(transition, "exitSetBools"));
			stream << " /* " << ATTR(transition, "exitSetBools") << " */ }" << std::endl;

			stream << "    }" << (i + 1 < _transitions.size() ? ",": "") << std::endl;
		}
		stream << "};" << std::endl;
		stream << std::endl;
	}

	stream << "#endif" << std::endl;
	stream << std::endl;

}

void ChartToC::writeCharArrayInitList(std::ostream& stream, const std::string& boolString) {
	/**
	 * 0111 -> 0x08
	 * 1111 -> 0x0f
	 * 1111 1111 -> 0xff
	 * 1111 1111 1110 -> 0x0f, 0xfd
	 *
	 * 76543210 fedcba98 ...
	 */

	std::string charArray;
	size_t index = 0;
	char currChar = 0;

	for (std::string::const_iterator bIter = boolString.begin(); bIter != boolString.end(); bIter++) {

		if (*bIter == '1') {
			currChar |= 1 << index;
		}

		index++;
		if (index == 8) {
			charArray += currChar;
			currChar = 0;
			index = 0;
		}
	}

	if (index != 0) {
		charArray += currChar;
	}

	std::string seperator = "";
	std::ios::fmtflags f(stream.flags());

	for (std::string::const_iterator cIter = charArray.begin(); cIter != charArray.end(); cIter++) {
		stream << seperator << "0x" << std::setw(2) << std::setfill('0') << std::hex << int(*cIter & 0xFF);
		seperator = ", ";
	}
	stream.flags(f);
}

void ChartToC::writeFSM(std::ostream& stream) {
	stream << "#ifndef USCXML_NO_STEP_FUNCTION" << std::endl;
	stream << "int uscxml_step(uscxml_ctx* ctx) {" << std::endl;
	stream << std::endl;

	stream << "    " << (_states.size() > _transitions.size() ? "USCXML_NR_STATES_TYPE" : "USCXML_NR_TRANS_TYPE") << " i, j, k;" << std::endl;
	stream << "    USCXML_NR_STATES_TYPE nr_states_bytes = ((USCXML_NUMBER_STATES + 7) & ~7) >> 3;" << std::endl;
	stream << "    USCXML_NR_TRANS_TYPE  nr_trans_bytes  = ((USCXML_NUMBER_TRANS + 7) & ~7) >> 3;" << std::endl;
	stream << "    int err = USCXML_ERR_OK;" << std::endl;

	stream << "    unsigned char conflicts  [USCXML_MAX_NR_TRANS_BYTES];" << std::endl;
	stream << "    unsigned char trans_set  [USCXML_MAX_NR_TRANS_BYTES];" << std::endl;
	stream << "    unsigned char target_set [USCXML_MAX_NR_STATES_BYTES];" << std::endl;
	stream << "    unsigned char exit_set   [USCXML_MAX_NR_STATES_BYTES];" << std::endl;
	stream << "    unsigned char entry_set  [USCXML_MAX_NR_STATES_BYTES];" << std::endl;
	stream << "    unsigned char tmp_states [USCXML_MAX_NR_STATES_BYTES];" << std::endl;
	stream << std::endl;

	stream << "#ifdef USCXML_VERBOSE" << std::endl;
	stream << "    printf(\"Config: \");" << std::endl;
	stream << "    printStateNames(ctx, ctx->config, USCXML_NUMBER_STATES);" << std::endl;
	stream << "#endif" << std::endl;
	stream << std::endl;

	stream << "    if (ctx->flags & USCXML_CTX_FINISHED)" << std::endl;
	stream << "        return USCXML_ERR_DONE;" << std::endl;
	stream << std::endl;

	stream << "    if (ctx->flags & USCXML_CTX_TOP_LEVEL_FINAL) {" << std::endl;
	stream << "        /* exit all remaining states */" << std::endl;
	stream << "        i = USCXML_NUMBER_STATES;" << std::endl;
	stream << "        while(i-- > 0) {" << std::endl;
	stream << "            if (BIT_HAS(i, ctx->config)) {" << std::endl;
	stream << "                /* call all on exit handlers */" << std::endl;
	stream << "                if (USCXML_GET_STATE(i).on_exit != NULL) {" << std::endl;
	stream << "                    if unlikely((err = USCXML_GET_STATE(i).on_exit(ctx, &USCXML_GET_STATE(i), ctx->event)) != USCXML_ERR_OK)" << std::endl;
	stream << "                        return err;" << std::endl;
	stream << "                }" << std::endl;
//	stream << "                BIT_CLEAR(i, ctx->config);" << std::endl;
	stream << "            }" << std::endl;
	stream << "            if (BIT_HAS(i, ctx->invocations)) {" << std::endl;
	stream << "                if (USCXML_GET_STATE(i).invoke != NULL)" << std::endl;
	stream << "                    USCXML_GET_STATE(i).invoke(ctx, &USCXML_GET_STATE(i), NULL, 1);" << std::endl;
	stream << "                BIT_CLEAR(i, ctx->invocations);" << std::endl;
	stream << "            }" << std::endl;
	stream << "        }" << std::endl;
	stream << "        ctx->flags |= USCXML_CTX_FINISHED;" << std::endl;
	stream << "        return USCXML_ERR_DONE;" << std::endl;
	stream << "    }" << std::endl;
	stream << std::endl;

	stream << "    bit_clear_all(target_set, nr_states_bytes);" << std::endl;
	stream << "    bit_clear_all(trans_set, nr_trans_bytes);" << std::endl;
	stream << "    if unlikely(ctx->flags == USCXML_CTX_PRISTINE) {" << std::endl;
	stream << "        if (ctx->machine->script != NULL)" << std::endl;
	stream << "            ctx->machine->script(ctx, &ctx->machine->states[0], NULL);" << std::endl;
	stream << "        bit_or(target_set, ctx->machine->states[0].completion, nr_states_bytes);" << std::endl;
	stream << "        ctx->flags |= USCXML_CTX_SPONTANEOUS | USCXML_CTX_INITIALIZED;" << std::endl;
	stream << "        goto ESTABLISH_ENTRY_SET;" << std::endl;
	stream << "    }" << std::endl;
	stream << std::endl;

	stream << "DEQUEUE_EVENT:" << std::endl;
	stream << "    if (ctx->flags & USCXML_CTX_SPONTANEOUS) {" << std::endl;
	stream << "        ctx->event = NULL;" << std::endl;
	stream << "        goto SELECT_TRANSITIONS;" << std::endl;
	stream << "    }" << std::endl;
	stream << "    if (ctx->dequeue_internal != NULL && (ctx->event = ctx->dequeue_internal(ctx)) != NULL) {" << std::endl;
	stream << "        goto SELECT_TRANSITIONS;" << std::endl;
	stream << "    }" << std::endl;
	stream << std::endl;

	stream << "    /* manage invocations */" << std::endl;
	stream << "    for (i = 0; i < USCXML_NUMBER_STATES; i++) {" << std::endl;
	stream << "        /* uninvoke */" << std::endl;
	stream << "        if (!BIT_HAS(i, ctx->config) && BIT_HAS(i, ctx->invocations)) {" << std::endl;
	stream << "            if (USCXML_GET_STATE(i).invoke != NULL)" << std::endl;
	stream << "                USCXML_GET_STATE(i).invoke(ctx, &USCXML_GET_STATE(i), NULL, 1);" << std::endl;
	stream << "            BIT_CLEAR(i, ctx->invocations)" << std::endl;
	stream << "        }" << std::endl;
	stream << "        /* invoke */" << std::endl;
	stream << "        if (BIT_HAS(i, ctx->config) && !BIT_HAS(i, ctx->invocations)) {" << std::endl;
	stream << "            if (USCXML_GET_STATE(i).invoke != NULL)" << std::endl;
	stream << "                USCXML_GET_STATE(i).invoke(ctx, &USCXML_GET_STATE(i), NULL, 0);" << std::endl;
	stream << "            BIT_SET_AT(i, ctx->invocations)" << std::endl;
	stream << "        }" << std::endl;
	stream << "    }" << std::endl;
	stream << std::endl;

	stream << "    if (ctx->dequeue_external != NULL && (ctx->event = ctx->dequeue_external(ctx)) != NULL) {" << std::endl;
	stream << "        goto SELECT_TRANSITIONS;" << std::endl;
	stream << "    }" << std::endl;
	stream << std::endl;
	stream << "    if (ctx->dequeue_external == NULL) {" << std::endl;
	stream << "        return USCXML_ERR_DONE;" << std::endl;
	stream << "    }" << std::endl;
	stream << "    return USCXML_ERR_IDLE;" << std::endl;
	stream << std::endl;

	stream << "SELECT_TRANSITIONS:" << std::endl;
	stream << "    bit_clear_all(conflicts, nr_trans_bytes);" << std::endl;
	stream << "    bit_clear_all(exit_set, nr_states_bytes);" << std::endl;
	stream << "    for (i = 0; i < USCXML_NUMBER_TRANS; i++) {" << std::endl;
	stream << "        /* never select history or initial transitions automatically */" << std::endl;
	stream << "        if unlikely(USCXML_GET_TRANS(i).type & (USCXML_TRANS_HISTORY | USCXML_TRANS_INITIAL))" << std::endl;
	stream << "            continue;" << std::endl;
	stream << std::endl;
	stream << "        /* is the transition active? */" << std::endl;
	stream << "        if (BIT_HAS(USCXML_GET_TRANS(i).source, ctx->config)) {" << std::endl;
	stream << "            /* is it non-conflicting? */" << std::endl;
	stream << "            if (!BIT_HAS(i, conflicts)) {" << std::endl;
	stream << "                /* is it spontaneous with an event or vice versa? */" << std::endl;
	stream << "                if ((USCXML_GET_TRANS(i).event == NULL && ctx->event == NULL) || " << std::endl;
	stream << "                    (USCXML_GET_TRANS(i).event != NULL && ctx->event != NULL)) {" << std::endl;
	stream << "                    /* is it enabled? */" << std::endl;
	stream << "                    if ((ctx->event == NULL || ctx->is_matched(ctx, &USCXML_GET_TRANS(i), ctx->event) > 0) &&" << std::endl;
	stream << "                        (USCXML_GET_TRANS(i).condition == NULL || " << std::endl;
	stream << "                         USCXML_GET_TRANS(i).is_enabled(ctx, &USCXML_GET_TRANS(i)) > 0)) {" << std::endl;
	stream << "                        /* remember that we found a transition */" << std::endl;
	stream << "                        ctx->flags |= USCXML_CTX_TRANSITION_FOUND;" << std::endl;
	stream << std::endl;

	stream << "                        /* transitions that are pre-empted */" << std::endl;
	stream << "                        bit_or(conflicts, USCXML_GET_TRANS(i).conflicts, nr_trans_bytes);" << std::endl;
	stream << std::endl;
	stream << "                        /* states that are directly targeted (resolve as entry-set later) */" << std::endl;
	stream << "                        bit_or(target_set, USCXML_GET_TRANS(i).target, nr_states_bytes);" << std::endl;
	stream << std::endl;
	stream << "                        /* states that will be left */" << std::endl;
	stream << "                        bit_or(exit_set, USCXML_GET_TRANS(i).exit_set, nr_states_bytes);" << std::endl;
	stream << std::endl;
	stream << "                        BIT_SET_AT(i, trans_set);" << std::endl;
	stream << "                    }" << std::endl;
	stream << "                }" << std::endl;
	stream << "            }" << std::endl;
	stream << "        }" << std::endl;
	stream << "    }" << std::endl;
	stream << "    bit_and(exit_set, ctx->config, nr_states_bytes);" << std::endl;
	stream << std::endl;

	stream << "    if (ctx->flags & USCXML_CTX_TRANSITION_FOUND) {" << std::endl;
	stream << "        ctx->flags |= USCXML_CTX_SPONTANEOUS;" << std::endl;
	stream << "        ctx->flags &= ~USCXML_CTX_TRANSITION_FOUND;" << std::endl;
	stream << "    } else {" << std::endl;
	stream << "        ctx->flags &= ~USCXML_CTX_SPONTANEOUS;" << std::endl;
	stream << "        goto DEQUEUE_EVENT;" << std::endl;
	stream << "    }" << std::endl;
	stream << std::endl;

	stream << "#ifdef USCXML_VERBOSE" << std::endl;
	stream << "    printf(\"Targets: \");" << std::endl;
	stream << "    printStateNames(ctx, target_set, USCXML_NUMBER_STATES);" << std::endl;
	stream << "#endif" << std::endl;
	stream << std::endl;

	stream << "#ifdef USCXML_VERBOSE" << std::endl;
	stream << "    printf(\"Exiting: \");" << std::endl;
	stream << "    printStateNames(ctx, exit_set, USCXML_NUMBER_STATES);" << std::endl;
	stream << "#endif" << std::endl;
	stream << std::endl;

	stream << "#ifdef USCXML_VERBOSE" << std::endl;
	stream << "    printf(\"History: \");" << std::endl;
	stream << "    printStateNames(ctx, ctx->history, USCXML_NUMBER_STATES);" << std::endl;
	stream << "#endif" << std::endl;
	stream << std::endl;

	stream << "/* REMEMBER_HISTORY: */" << std::endl;
	stream << "    for (i = 0; i < USCXML_NUMBER_STATES; i++) {" << std::endl;
	stream << "        if unlikely(USCXML_STATE_MASK(USCXML_GET_STATE(i).type) == USCXML_STATE_HISTORY_SHALLOW ||" << std::endl;
	stream << "                    USCXML_STATE_MASK(USCXML_GET_STATE(i).type) == USCXML_STATE_HISTORY_DEEP) {" << std::endl;
	stream << "            /* a history state whose parent is about to be exited */" << std::endl;
	stream << "            if unlikely(BIT_HAS(USCXML_GET_STATE(i).parent, exit_set)) {" << std::endl;
	stream << "                bit_copy(tmp_states, USCXML_GET_STATE(i).completion, nr_states_bytes);" << std::endl;
	stream << std::endl;
	stream << "                /* set those states who were enabled */" << std::endl;
	stream << "                bit_and(tmp_states, ctx->config, nr_states_bytes);" << std::endl;
	stream << std::endl;
	stream << "                /* clear current history with completion mask */" << std::endl;
	stream << "                bit_and_not(ctx->history, USCXML_GET_STATE(i).completion, nr_states_bytes);" << std::endl;
	stream << std::endl;
	stream << "                /* set history */" << std::endl;
	stream << "                bit_or(ctx->history, tmp_states, nr_states_bytes);" << std::endl;
	stream << "            }" << std::endl;
	stream << "        }" << std::endl;
	stream << "    }" << std::endl;
	stream << std::endl;

	stream << "ESTABLISH_ENTRY_SET:" << std::endl;
	stream << "    /* calculate new entry set */" << std::endl;
	stream << "    bit_copy(entry_set, target_set, nr_states_bytes);" << std::endl;
	stream << std::endl;
	stream << "    /* iterate for ancestors */" << std::endl;
	stream << "    for (i = 0; i < USCXML_NUMBER_STATES; i++) {" << std::endl;
	stream << "        if (BIT_HAS(i, entry_set)) {" << std::endl;
	stream << "            bit_or(entry_set, USCXML_GET_STATE(i).ancestors, nr_states_bytes);" << std::endl;
	stream << "        }" << std::endl;
	stream << "    }" << std::endl;
	stream << std::endl;

	stream << "    /* iterate for descendants */" << std::endl;
	stream << "    for (i = 0; i < USCXML_NUMBER_STATES; i++) {" << std::endl;
	stream << "        if (BIT_HAS(i, entry_set)) {" << std::endl;
	stream << "            switch (USCXML_STATE_MASK(USCXML_GET_STATE(i).type)) {" << std::endl;
	stream << "                case USCXML_STATE_PARALLEL: {" << std::endl;
	stream << "                    bit_or(entry_set, USCXML_GET_STATE(i).completion, nr_states_bytes);" << std::endl;
	stream << "                    break;" << std::endl;
	stream << "                }" << std::endl;
	stream << "                case USCXML_STATE_HISTORY_SHALLOW:" << std::endl;
	stream << "                case USCXML_STATE_HISTORY_DEEP: {" << std::endl;
	stream << "                    if (!bit_has_and(USCXML_GET_STATE(i).completion, ctx->history, nr_states_bytes) &&" << std::endl;
	stream << "                        !BIT_HAS(USCXML_GET_STATE(i).parent, ctx->config)) {" << std::endl;
	stream << "                        /* nothing set for history, look for a default transition */" << std::endl;
	stream << "                        for (j = 0; j < USCXML_NUMBER_TRANS; j++) {" << std::endl;
	stream << "                            if unlikely(ctx->machine->transitions[j].source == i) {" << std::endl;
	stream << "                                bit_or(entry_set, ctx->machine->transitions[j].target, nr_states_bytes);" << std::endl;
	stream << "                                if(USCXML_STATE_MASK(USCXML_GET_STATE(i).type) == USCXML_STATE_HISTORY_DEEP &&" << std::endl;
	stream << "                                   !bit_has_and(ctx->machine->transitions[j].target, USCXML_GET_STATE(i).children, nr_states_bytes)) {" << std::endl;
	stream << "                                    for (k = i + 1; k < USCXML_NUMBER_STATES; k++) {" << std::endl;
	stream << "                                        if (BIT_HAS(k, ctx->machine->transitions[j].target)) {" << std::endl;
	stream << "                                            bit_or(entry_set, ctx->machine->states[k].ancestors, nr_states_bytes);" << std::endl;
	stream << "                                            break;" << std::endl;
	stream << "                                        }" << std::endl;
	stream << "                                    }" << std::endl;
	stream << "                                }" << std::endl;
	stream << "                                BIT_SET_AT(j, trans_set);" << std::endl;
	stream << "                                break;" << std::endl;
	stream << "                            }" << std::endl;
	stream << "                            /* Note: SCXML mandates every history to have a transition! */" << std::endl;
	stream << "                        }" << std::endl;
	stream << "                    } else {" << std::endl;
	stream << "                        bit_copy(tmp_states, USCXML_GET_STATE(i).completion, nr_states_bytes);" << std::endl;
	stream << "                        bit_and(tmp_states, ctx->history, nr_states_bytes);" << std::endl;
	stream << "                        bit_or(entry_set, tmp_states, nr_states_bytes);" << std::endl;
	stream << "                        if (USCXML_GET_STATE(i).type == (USCXML_STATE_HAS_HISTORY | USCXML_STATE_HISTORY_DEEP)) {" << std::endl;
	stream << "                            /* a deep history state with nested histories -> more completion */" << std::endl;
	stream << "                            for (j = i + 1; j < USCXML_NUMBER_STATES; j++) {" << std::endl;
	stream << "                                if (BIT_HAS(j, USCXML_GET_STATE(i).completion) &&" << std::endl;
	stream << "                                    BIT_HAS(j, entry_set) &&" << std::endl;
	stream << "                                    (ctx->machine->states[j].type & USCXML_STATE_HAS_HISTORY)) {" << std::endl;
	stream << "                                    for (k = j + 1; k < USCXML_NUMBER_STATES; k++) {" << std::endl;
	stream << "                                        /* add nested history to entry_set */" << std::endl;
	stream << "                                        if ((USCXML_STATE_MASK(ctx->machine->states[k].type) == USCXML_STATE_HISTORY_DEEP ||" << std::endl;
	stream << "                                             USCXML_STATE_MASK(ctx->machine->states[k].type) == USCXML_STATE_HISTORY_SHALLOW) &&" << std::endl;
	stream << "                                            BIT_HAS(k, ctx->machine->states[j].children)) {" << std::endl;
	stream << "                                            /* a nested history state */" << std::endl;
	stream << "                                            BIT_SET_AT(k, entry_set);" << std::endl;
	stream << "                                        }" << std::endl;
	stream << "                                    }" << std::endl;
	stream << "                                }" << std::endl;
	stream << "                            }" << std::endl;
	stream << "                        }" << std::endl;
	stream << "                    }" << std::endl;
	stream << "                    break;" << std::endl;
	stream << "                }" << std::endl;
	stream << "                case USCXML_STATE_INITIAL: {" << std::endl;
	stream << "                    for (j = 0; j < USCXML_NUMBER_TRANS; j++) {" << std::endl;
	stream << "                        if (ctx->machine->transitions[j].source == i) {" << std::endl;
	stream << "                            BIT_SET_AT(j, trans_set);" << std::endl;
	stream << "                            BIT_CLEAR(i, entry_set);" << std::endl;
	stream << "                            bit_or(entry_set, ctx->machine->transitions[j].target, nr_states_bytes);" << std::endl;
	stream << "                            for (k = i + 1; k < USCXML_NUMBER_STATES; k++) {" << std::endl;
	stream << "                                if (BIT_HAS(k, ctx->machine->transitions[j].target)) {" << std::endl;
	stream << "                                    bit_or(entry_set, ctx->machine->states[k].ancestors, nr_states_bytes);" << std::endl;
	stream << "                                }" << std::endl;
	stream << "                            }" << std::endl;
	stream << "                        }" << std::endl;
	stream << "                    }" << std::endl;
	stream << "                    break;" << std::endl;
	stream << "                }" << std::endl;
	stream << "                case USCXML_STATE_COMPOUND: { /* we need to check whether one child is already in entry_set */" << std::endl;
	stream << "                    if (!bit_has_and(entry_set, USCXML_GET_STATE(i).children, nr_states_bytes) &&" << std::endl;
	stream << "                        (!bit_has_and(ctx->config, USCXML_GET_STATE(i).children, nr_states_bytes) ||" << std::endl;
	stream << "                         bit_has_and(exit_set, USCXML_GET_STATE(i).children, nr_states_bytes)))" << std::endl;
	stream << "                    {" << std::endl;
	stream << "                        bit_or(entry_set, USCXML_GET_STATE(i).completion, nr_states_bytes);" << std::endl;
	stream << "                        if (!bit_has_and(USCXML_GET_STATE(i).completion, USCXML_GET_STATE(i).children, nr_states_bytes)) {" << std::endl;
	stream << "                            /* deep completion */" << std::endl;
	stream << "                            for (j = i + 1; j < USCXML_NUMBER_STATES; j++) {" << std::endl;
	stream << "                                if (BIT_HAS(j, USCXML_GET_STATE(i).completion)) {" << std::endl;
	stream << "                                    bit_or(entry_set, ctx->machine->states[j].ancestors, nr_states_bytes);" << std::endl;
	stream << "                                    break; /* completion of compound is single state */" << std::endl;
	stream << "                                }" << std::endl;
	stream << "                            }" << std::endl;
	stream << "                        }" << std::endl;
	stream << "                    }" << std::endl;
	stream << "                    break;" << std::endl;
	stream << "                }" << std::endl;
	stream << "            }" << std::endl;
	stream << "        }" << std::endl;
	stream << "    }" << std::endl;
	stream << std::endl;

	stream << "#ifdef USCXML_VERBOSE" << std::endl;
	stream << "    printf(\"Transitions: \");" << std::endl;
	stream << "    printBitsetIndices(trans_set, sizeof(char) * 8 * nr_trans_bytes);" << std::endl;
	stream << "#endif" << std::endl;
	stream << std::endl;

	stream << "/* EXIT_STATES: */" << std::endl;
	stream << "    i = USCXML_NUMBER_STATES;" << std::endl;
	stream << "    while(i-- > 0) {" << std::endl;
	stream << "        if (BIT_HAS(i, exit_set) && BIT_HAS(i, ctx->config)) {" << std::endl;
	stream << "            /* call all on exit handlers */" << std::endl;
	stream << "            if (USCXML_GET_STATE(i).on_exit != NULL) {" << std::endl;
	stream << "                if unlikely((err = USCXML_GET_STATE(i).on_exit(ctx, &USCXML_GET_STATE(i), ctx->event)) != USCXML_ERR_OK)" << std::endl;
	stream << "                    return err;" << std::endl;
	stream << "            }" << std::endl;
	stream << "            BIT_CLEAR(i, ctx->config);" << std::endl;
	stream << "        }" << std::endl;
	stream << "    }" << std::endl;
	stream << std::endl;

	stream << "/* TAKE_TRANSITIONS: */" << std::endl;
	stream << "    for (i = 0; i < USCXML_NUMBER_TRANS; i++) {" << std::endl;
	stream << "        if (BIT_HAS(i, trans_set) && (USCXML_GET_TRANS(i).type & (USCXML_TRANS_HISTORY | USCXML_TRANS_INITIAL)) == 0) {" << std::endl;
	stream << "            /* call executable content in transition */" << std::endl;
	stream << "            if (USCXML_GET_TRANS(i).on_transition != NULL) {" << std::endl;
	stream << "                if unlikely((err = USCXML_GET_TRANS(i).on_transition(ctx," << std::endl;
	stream << "                                                                              &ctx->machine->states[USCXML_GET_TRANS(i).source]," << std::endl;
	stream << "                                                                              ctx->event)) != USCXML_ERR_OK)" << std::endl;
	stream << "                    return err;" << std::endl;
	stream << "            }" << std::endl;
	stream << "        }" << std::endl;
	stream << "    }" << std::endl;
	stream << std::endl;

	stream << "#ifdef USCXML_VERBOSE" << std::endl;
	stream << "    printf(\"Entering: \");" << std::endl;
	stream << "    printStateNames(ctx, entry_set, USCXML_NUMBER_STATES);" << std::endl;
	stream << "#endif" << std::endl;
	stream << std::endl;

	stream << "/* ENTER_STATES: */" << std::endl;
	stream << "    for (i = 0; i < USCXML_NUMBER_STATES; i++) {" << std::endl;
	stream << "        if (BIT_HAS(i, entry_set) && !BIT_HAS(i, ctx->config)) {" << std::endl;
	stream << "            /* these are no proper states */" << std::endl;
	stream << "            if unlikely(USCXML_STATE_MASK(USCXML_GET_STATE(i).type) == USCXML_STATE_HISTORY_DEEP ||" << std::endl;
	stream << "                        USCXML_STATE_MASK(USCXML_GET_STATE(i).type) == USCXML_STATE_HISTORY_SHALLOW ||" << std::endl;
	stream << "                        USCXML_STATE_MASK(USCXML_GET_STATE(i).type) == USCXML_STATE_INITIAL)" << std::endl;
	stream << "                continue;" << std::endl;
	stream << std::endl;

	stream << "            BIT_SET_AT(i, ctx->config);" << std::endl;
	stream << std::endl;

	stream << "            /* initialize data */" << std::endl;
	stream << "            if (!BIT_HAS(i, ctx->initialized_data)) {" << std::endl;
	stream << "                if unlikely(USCXML_GET_STATE(i).data != NULL && ctx->exec_content_init != NULL) {" << std::endl;
	stream << "                    ctx->exec_content_init(ctx, USCXML_GET_STATE(i).data);" << std::endl;
	stream << "                }" << std::endl;
	stream << "                BIT_SET_AT(i, ctx->initialized_data);" << std::endl;
	stream << "            }" << std::endl;
	stream << std::endl;

	stream << "            if (USCXML_GET_STATE(i).on_entry != NULL) {" << std::endl;
	stream << "                if unlikely((err = USCXML_GET_STATE(i).on_entry(ctx, &USCXML_GET_STATE(i), ctx->event)) != USCXML_ERR_OK)" << std::endl;
	stream << "                    return err;" << std::endl;
	stream << "            }" << std::endl;
	stream << std::endl;

	stream << "            /* take history and initial transitions */" << std::endl;
	stream << "            for (j = 0; j < USCXML_NUMBER_TRANS; j++) {" << std::endl;
	stream << "                if unlikely(BIT_HAS(j, trans_set) &&" << std::endl;
	stream << "                            (ctx->machine->transitions[j].type & (USCXML_TRANS_HISTORY | USCXML_TRANS_INITIAL)) &&" << std::endl;
	stream << "                            ctx->machine->states[ctx->machine->transitions[j].source].parent == i) {" << std::endl;
	stream << "                    /* call executable content in transition */" << std::endl;
	stream << "                    if (ctx->machine->transitions[j].on_transition != NULL) {" << std::endl;
	stream << "                        if unlikely((err = ctx->machine->transitions[j].on_transition(ctx," << std::endl;
	stream << "                                                                                      &USCXML_GET_STATE(i)," << std::endl;
	stream << "                                                                                      ctx->event)) != USCXML_ERR_OK)" << std::endl;
	stream << "                            return err;" << std::endl;
	stream << "                    }" << std::endl;
	stream << "                }" << std::endl;
	stream << "            }" << std::endl;
	stream << std::endl;

	stream << "            /* handle final states */" << std::endl;
	stream << "            if unlikely(USCXML_STATE_MASK(USCXML_GET_STATE(i).type) == USCXML_STATE_FINAL) {" << std::endl;
	stream << "                if unlikely(USCXML_GET_STATE(i).ancestors[0] == 0x01) {" << std::endl;
	stream << "                    ctx->flags |= USCXML_CTX_TOP_LEVEL_FINAL;" << std::endl;
	stream << "                } else {" << std::endl;
	stream << "                    /* raise done event */" << std::endl;
	stream << "                    const uscxml_elem_donedata* donedata = &ctx->machine->donedata[0];" << std::endl;
	stream << "                    while(USCXML_ELEM_DONEDATA_IS_SET(donedata)) {" << std::endl;
	stream << "                        if unlikely(donedata->source == i)" << std::endl;
	stream << "                            break;" << std::endl;
	stream << "                        donedata++;" << std::endl;
	stream << "                    }" << std::endl;
	stream << "                    ctx->raise_done_event(ctx, &ctx->machine->states[USCXML_GET_STATE(i).parent], (USCXML_ELEM_DONEDATA_IS_SET(donedata) ? donedata : NULL));" << std::endl;
	stream << "                }" << std::endl;
	stream << std::endl;

	stream << "                /**" << std::endl;
	stream << "                 * are we the last final state to leave a parallel state?:" << std::endl;
	stream << "                 * 1. Gather all parallel states in our ancestor chain" << std::endl;
	stream << "                 * 2. Find all states for which these parallels are ancestors" << std::endl;
	stream << "                 * 3. Iterate all active final states and remove their ancestors" << std::endl;
	stream << "                 * 4. If a state remains, not all children of a parallel are final" << std::endl;
	stream << "                 */" << std::endl;
	stream << "                for (j = 0; j < USCXML_NUMBER_STATES; j++) {" << std::endl;
	stream << "                    if unlikely(USCXML_STATE_MASK(ctx->machine->states[j].type) == USCXML_STATE_PARALLEL &&" << std::endl;
	stream << "                                BIT_HAS(j, USCXML_GET_STATE(i).ancestors)) {" << std::endl;
	stream << "                        bit_clear_all(tmp_states, nr_states_bytes);" << std::endl;
	stream << "                        for (k = 0; k < USCXML_NUMBER_STATES; k++) {" << std::endl;
	stream << "                            if unlikely(BIT_HAS(j, ctx->machine->states[k].ancestors) && BIT_HAS(k, ctx->config)) {" << std::endl;
	stream << "                                if (USCXML_STATE_MASK(ctx->machine->states[k].type) == USCXML_STATE_FINAL) {" << std::endl;
	stream << "                                    bit_and_not(tmp_states, ctx->machine->states[k].ancestors, nr_states_bytes);" << std::endl;
	stream << "                                } else {" << std::endl;
	stream << "                                    BIT_SET_AT(k, tmp_states);" << std::endl;
	stream << "                                }" << std::endl;
	stream << "                            }" << std::endl;
	stream << "                        }" << std::endl;
	stream << "                        if unlikely(!bit_has_any(tmp_states, nr_states_bytes)) {" << std::endl;
	stream << "                            ctx->raise_done_event(ctx, &ctx->machine->states[j], NULL);" << std::endl;
	stream << "                        }" << std::endl;
	stream << "                    }" << std::endl;
	stream << "                }" << std::endl;
	stream << std::endl;

	stream << "            }" << std::endl;
	stream << std::endl;

	stream << "        }" << std::endl;
	stream << "    }" << std::endl;
	stream << std::endl;

	stream << "    return USCXML_ERR_OK;" << std::endl;
	stream << "}" << std::endl;
	stream << std::endl;

	stream << "#define USCXML_NO_STEP_FUNCTION" << std::endl;
	stream << "#endif" << std::endl;
	stream << std::endl;
}

ChartToC::~ChartToC() {
}

}
