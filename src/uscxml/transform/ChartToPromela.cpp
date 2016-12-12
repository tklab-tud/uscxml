/**
 *  @file
 *  @author   2012-2014 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#include "uscxml/transform/ChartToPromela.h"
#include "uscxml/util/Predicates.h"
#include "uscxml/util/String.h"
#include "uscxml/plugins/datamodel/promela/PromelaParser.h"
#include "uscxml/plugins/datamodel/promela/parser/promela.tab.hpp"

#include <boost/algorithm/string.hpp>
#include "uscxml/interpreter/Logging.h"

#include <algorithm>
#include <cmath>

#define ADAPT_SRC(code) _analyzer->adaptCode(code, _prefix)
#define BIT_WIDTH(number) (number > 1 ? (int)ceil(log2((double)number)) : 1)
#define EVENT_NAME (_analyzer->usesComplexEventStruct() ? "_event.name" : "_event")
#define TMP_EVENT_NAME (_analyzer->usesComplexEventStruct() ? "_tmpE.name" : "_tmpE")
#define MAX(X,Y) ((X) > (Y) ? (X) : (Y))

#define TRACE_PML

#ifdef TRACE_PML
#define TRACE_EXECUTION_V(fmt, ...) \
stream << std::endl; \
stream << "#if TRACE_EXECUTION" << std::endl; \
if (_machinesAll->size() > 1) {\
    stream << "printf(\"%d: " fmt "\\n\", _pid, " __VA_ARGS__ ");" << std::endl; \
} else { \
    stream << "printf(\"" fmt "\\n\", " __VA_ARGS__ ");" << std::endl; \
} \
stream << "#endif" << std::endl; \
stream << std::endl;

#define TRACE_EXECUTION(fmt) \
stream << std::endl; \
stream << "#if TRACE_EXECUTION" << std::endl; \
if (_machinesAll->size() > 1) {\
stream << "printf(\"%d: " fmt "\\n\", _pid);" << std::endl; \
} else { \
stream << "printf(\"" fmt "\\n\");" << std::endl; \
} \
stream << "#endif" << std::endl; \
stream << std::endl;

#else

#define TRACE_EXECUTION_V(fmt, ...)
#define TRACE_EXECUTION(fmt)
#endif

namespace uscxml {

using namespace XERCESC_NS;


Transformer ChartToPromela::transform(const Interpreter& other) {
	return std::shared_ptr<TransformerImpl>(new ChartToPromela(other));
}

ChartToPromela::~ChartToPromela() {
}

void ChartToPromela::prepare() {
	if (_machinesAll == NULL) {
		_machinesAll = new std::map<DOMElement*, ChartToPromela*>();
		(*_machinesAll)[_scxml] = this;
	}

	if (_machinesAllPerId == NULL)
		_machinesAllPerId = new std::map<std::string, XERCESC_NS::DOMElement* >();

	if (_parentTopMost == NULL) {
		_parentTopMost = this;
	}

	// are there nested SCXML invokers?
	std::list<DOMElement*> invokes = DOMUtils::inDocumentOrder({ XML_PREFIX(_scxml).str() + "invoke" }, _scxml);
	for (auto invoke : invokes) {

		if (!HAS_ATTR(invoke, "id")) {
			invoke->setAttribute(X("id"), X("INV_" + UUID::getUUID().substr(0,5)));
		} else if (HAS_ATTR(invoke, "id") && UUID::isUUID(ATTR(invoke, "id"))) {
			// shorten UUIDs
			invoke->setAttribute(X("id"), X("INV_" + ATTR(invoke, "id").substr(0,5)));
		}

		if (HAS_ATTR(invoke, "type") &&
		        ATTR(invoke, "type") != "scxml" &&
		        ATTR(invoke, "type") != "http://www.w3.org/TR/scxml/" &&
		        ATTR(invoke, "type") != "http://www.w3.org/TR/scxml/#SCXMLEventProcessor")
			continue;

		assert(HAS_ATTR(invoke, "id"));
		invoke->setAttribute(X("name"), invoke->getAttribute(X("id")));

		Interpreter nested;
		if (HAS_ATTR(invoke, "src")) {
			nested = Interpreter::fromURL(URL::resolve(ATTR(invoke, "src"), _baseURL));
		} else {
			std::list<DOMElement*> contents = DOMUtils::filterChildElements(XML_PREFIX(invoke).str() + "content", invoke);
			std::list<DOMElement*> scxmls = DOMUtils::filterChildElements(XML_PREFIX(invoke).str() + "scxml", contents.front());

			assert (scxmls.size() > 0);
			nested = Interpreter::fromElement(scxmls.front(), _baseURL);
		}

		_machinesNested[invoke] = new ChartToPromela(nested);
		_machinesNested[invoke]->_analyzer = _analyzer;
		_machinesNested[invoke]->_analyzer->analyze(_machinesNested[invoke]);
		_machinesNested[invoke]->prepare();
		_machinesNested[invoke]->_parent = this;
		_machinesNested[invoke]->_parentTopMost = _parentTopMost;
		_machinesNested[invoke]->_machinesAll = _machinesAll;
		(*_machinesAll)[invoke] = _machinesNested[invoke];

		_machinesNested[invoke]->_invokerid = ATTR(invoke, "id");
		_analyzer->createMacroName(_machinesNested[invoke]->_invokerid);
		_analyzer->addEvent("done.invoke." + _machinesNested[invoke]->_invokerid);

		_machinesNested[invoke]->_prefix = _analyzer->macroForLiteral(ATTR(invoke, "id")) + "_";


		_machinesPerId[ATTR_CAST(invoke, "id")] = invoke;
		(*_machinesAllPerId)[ATTR(invoke, "id")] = invoke;

	}

	if (_machinesAll->size() > 1) {
//        _analyzer->addCode("_event.origin", this);
		_analyzer->addCode("_event.invokeid", this);
	}

	// transform data / assign json into PROMELA statements
	std::list<DOMElement*> values;
	values.splice(values.end(), DOMUtils::inDocumentOrder({XML_PREFIX(_scxml).str() + "assign"}, _scxml));
	values.splice(values.end(), DOMUtils::inDocumentOrder({XML_PREFIX(_scxml).str() + "data"}, _scxml));

	for (auto element : values) {
		std::string key;
		if (HAS_ATTR(element, "id")) {
			key = ATTR(element, "id");
		} else if (HAS_ATTR(element, "location")) {
			key = ATTR(element, "location");
		}

		if (key.length() == 0)
			continue;

		std::string value;
		if (HAS_ATTR(element, "expr")) {
			value = ATTR(element, "expr");
		} else if (HAS_ATTR(element, "src")) {
			URL absUrl = URL::resolve(ATTR_CAST(element, "src"), _baseURL);
			value = absUrl.getInContent();
		} else {
			std::list<DOMNode*> assignTexts = DOMUtils::filterChildType(DOMNode::TEXT_NODE, element, true);
			if (assignTexts.size() > 0) {
				for (auto assignText : assignTexts) {
					value += X(assignText->getNodeValue()).str();
				}
			}
		}

		boost::trim(value);
		if (value.size() == 0)
			continue;

		// remove all children, we will replace by suitable promela statements
		while(element->hasChildNodes())
			element->removeChild(element->getFirstChild());

		std::string newValue;
		Data json = Data::fromJSON(value);
		if (!json.empty()) {
			newValue = dataToAssignments(key, json);
		} else {
			newValue = key + " = " + value + ";";
		}

		if (LOCALNAME(element) == "data")
			_varInitializers.push_back(newValue);

		DOMText* newText = _document->createTextNode(X(newValue));
		element->insertBefore(newText, NULL);

		_analyzer->addCode(newValue, this);

	}
}

void ChartToPromela::writeTo(std::ostream& stream) {
	_prefix = "ROOT_";
	_invokerid = "ROOT";
	_analyzer = new PromelaCodeAnalyzer();
	_analyzer->analyze(this);
	_analyzer->createMacroName(_invokerid);
	prepare();

	stream << "/** generated from " << std::endl;
	stream << "  " << std::string(_baseURL) << std::endl;
	stream << "  Verify as:" << std::endl;
	stream << "  $ spin -a this.pml" << std::endl;
	stream << "  $ gcc -DMEMLIM=1024 -DVECTORSZ=8192 -O2 -DXUSAFE pan.c -o pan" << std::endl;
	stream << "  $ ./pan -a -m10000 -n -N w3c" << std::endl;
	stream << " */" << std::endl;
	stream << std::endl;


	writeMacros(stream);
	stream << std::endl;
	writeStrings(stream);
	stream << std::endl;

	for (auto machine : *_machinesAll) {
		machine.second->writeBitHasAndMacro(stream);
		stream << std::endl;
		machine.second->writeBitHasAnyMacro(stream);
		stream << std::endl;
		machine.second->writeBitOrMacro(stream);
		stream << std::endl;
		machine.second->writeBitClearMacro(stream);
		stream << std::endl;
		machine.second->writeBitCopyMacro(stream);
		stream << std::endl;
		machine.second->writeBitAndMacro(stream);
		stream << std::endl;
		machine.second->writeBitAndNotMacro(stream);
		stream << std::endl;
		writeTypeDefs(stream);
		stream << std::endl;

	}

	writeCommonTypeDefs(stream);
	stream << std::endl;

	for (auto machine : *_machinesAll) {
		machine.second->writeVariables(stream);
		stream << std::endl;
	}
	writeCommonVariables(stream);
	stream << std::endl;

	if (_analyzer->usesComplexEventStruct()) {
		if (_analyzer->usesEventField("delay")) {
			writeInsertWithDelay(stream);
			stream << std::endl;
		}
		writeAdvanceTime(stream);
		stream << std::endl;
		writeScheduleMachines(stream);
		stream << std::endl;
		writeRescheduleProcess(stream);
		stream << std::endl;
		writeDetermineShortestDelay(stream);
		stream << std::endl;
	}

	if (_machinesAll->size() > 1) {
		writeRemovePendingEventsFromInvoker(stream);
		stream << std::endl;
	}

	writeCancelEvents(stream);
	stream << std::endl;

	for (auto machine : *_machinesAll) {
		machine.second->writeFSM(stream);
		stream << std::endl;
	}


	stream << "init {" << std::endl;

	stream << "/* initialize state and transition information */" << std::endl;
	for (auto machine : *_machinesAll) {
		machine.second->writeTransitions(stream);
		stream << std::endl;
		machine.second->writeStates(stream);
		stream << std::endl;

		stream << "/* initialize data model variables */" << std::endl;
		stream << "  " << machine.second->_prefix << "flags[USCXML_CTX_PRISTINE]  = true;" << std::endl;
		stream << "  " << machine.second->_prefix << "flags[USCXML_CTX_SPONTANEOUS] = true;" << std::endl;

		for (auto initializer : machine.second->_varInitializers) {
			stream << _analyzer->adaptCode(beautifyIndentation(initializer, 1), machine.second->_prefix) << std::endl;
		}
	}

	stream << std::endl;

	stream << "  run " << _prefix << "step() priority 10;" << std::endl;
	stream << "}" << std::endl;
	stream << std::endl;
	stream << "ltl w3c { eventually (" << _prefix << "config[" << _prefix << "PASS]) }" << std::endl;

}

void ChartToPromela::writeBitAndMacro(std::ostream& stream) {
	stream << "/** and'ing bits in a with mask */" << std::endl;
	stream << "#define " << _prefix << "TRANS_AND(a, mask) \\" << std::endl;
	for (size_t i = 0; i < _transitions.size(); i++) {
		stream << "a[" << i << "] = a[" << i << "] & mask[" << i << "]; \\" << std::endl;
	}
	stream << std::endl;

	stream << "#define " << _prefix << "STATES_AND(a, mask) \\" << std::endl;
	for (size_t i = 0; i < _states.size(); i++) {
		stream << "a[" << i << "] = a[" << i << "] & mask[" << i << "]; \\" << std::endl;
	}
	stream << std::endl;

}

void ChartToPromela::writeBitAndNotMacro(std::ostream& stream) {
	stream << "/** not and'ing bits in a with mask */" << std::endl;
	stream << "#define " << _prefix << "TRANS_AND_NOT(a, mask) \\" << std::endl;
	for (size_t i = 0; i < _transitions.size(); i++) {
		stream << "a[" << i << "] = a[" << i << "] & !mask[" << i << "]; \\" << std::endl;
	}
	stream << std::endl;

	stream << "#define " << _prefix << "STATES_AND_NOT(a, mask) \\" << std::endl;
	for (size_t i = 0; i < _states.size(); i++) {
		stream << "a[" << i << "] = a[" << i << "] & !mask[" << i << "]; \\" << std::endl;
	}
	stream << std::endl;

}

void ChartToPromela::writeBitCopyMacro(std::ostream& stream) {
	stream << "/** copy bits from a to b */" << std::endl;
	stream << "#define " << _prefix << "TRANS_COPY(a, b) \\" << std::endl;
	for (size_t i = 0; i < _transitions.size(); i++) {
		stream << "a[" << i << "] = b[" << i << "]; \\" << std::endl;
	}
	stream << std::endl;

	stream << "#define " << _prefix << "STATES_COPY(a, b) \\" << std::endl;
	for (size_t i = 0; i < _states.size(); i++) {
		stream << "a[" << i << "] = b[" << i << "]; \\" << std::endl;
	}
	stream << std::endl;


}

void ChartToPromela::writeBitHasAndMacro(std::ostream& stream) {
	stream << "/** is there a common bit in t1 and t2 */" << std::endl;
	stream << "#define " << _prefix << "TRANS_HAS_AND(a, b) \\" << std::endl;

	stream << "(false \\" << std::endl;
	for (size_t i = 0; i < _transitions.size(); i++) {
		stream << " || a[" << i << "] & b[" << i << "] \\" << std::endl;
	}
	stream << ")" << std::endl;
	stream << std::endl;

	stream << "#define " << _prefix << "STATES_HAS_AND(a, b) \\" << std::endl;

	stream << "(false \\" << std::endl;
	for (size_t i = 0; i < _states.size(); i++) {
		stream << " || a[" << i << "] & b[" << i << "] \\" << std::endl;
	}
	stream << ")" << std::endl;
	stream << std::endl;

}

void ChartToPromela::writeBitHasAnyMacro(std::ostream& stream) {
	stream << "/** is there bit set in a */" << std::endl;
	stream << "#define " << _prefix << "TRANS_HAS_ANY(a) \\" << std::endl;

	stream << "(false \\" << std::endl;
	for (size_t i = 0; i < _transitions.size(); i++) {
		stream << " || a[" << i << "] \\" << std::endl;
	}
	stream << ")" << std::endl;
	stream << std::endl;

	stream << "#define " << _prefix << "STATES_HAS_ANY(a) \\" << std::endl;

	stream << "(false \\" << std::endl;
	for (size_t i = 0; i < _states.size(); i++) {
		stream << " || a[" << i << "] \\" << std::endl;
	}
	stream << ")" << std::endl;
	stream << std::endl;

}

void ChartToPromela::writeBitOrMacro(std::ostream& stream) {
	stream << "/** or'ing bits in a with mask */" << std::endl;
	stream << "#define " << _prefix << "TRANS_OR(a, mask) \\" << std::endl;
	for (size_t i = 0; i < _transitions.size(); i++) {
		stream << "a[" << i << "] = a[" << i << "] | mask[" << i << "]; \\" << std::endl;
	}
	stream << std::endl;

	stream << "#define " << _prefix << "STATES_OR(a, mask) \\" << std::endl;
	for (size_t i = 0; i < _states.size(); i++) {
		stream << "a[" << i << "] = a[" << i << "] | mask[" << i << "]; \\" << std::endl;
	}
	stream << std::endl;

}

void ChartToPromela::writeBitClearMacro(std::ostream& stream) {
	stream << "/** clearing all bits of a */" << std::endl;
	stream << "#define " << _prefix << "TRANS_CLEAR(a) \\" << std::endl;
	for (size_t i = 0; i < _transitions.size(); i++) {
		stream << "a[" << i << "] = false; \\" << std::endl;
	}
	stream << std::endl;

	stream << "#define " << _prefix << "STATES_CLEAR(a) \\" << std::endl;
	for (size_t i = 0; i < _states.size(); i++) {
		stream << "a[" << i << "] = false; \\" << std::endl;
	}
	stream << std::endl;

}

void ChartToPromela::printBitArray(std::ostream& stream,
                                   const std::string& array,
                                   size_t length,
                                   size_t indent) {
	std::string padding;
	while (indent--)
		padding += "  ";

	stream << padding << "printf(\"";
	for (size_t i = 0; i < length; i++) {
		stream << "%d";
	}
	stream << "\", " << std::endl;
	for (size_t i = 0; i < length; i++) {
		stream << padding << "    " << array << "[" << toStr(i) << "]";
		if (i + 1 < length) {
			stream << ", " << std::endl;
		}
	}
	stream << ");" << std::endl;
}

void ChartToPromela::writeMacros(std::ostream& stream) {
	stream << "/* machine state flags */" << std::endl;
	stream << "#define USCXML_CTX_PRISTINE          0 /* can be out-factored */" << std::endl;
	stream << "#define USCXML_CTX_SPONTANEOUS       1" << std::endl;
	stream << "#define USCXML_CTX_TOP_LEVEL_FINAL   2" << std::endl;
	stream << "#define USCXML_CTX_TRANSITION_FOUND  3" << std::endl;
	stream << "#define USCXML_CTX_FINISHED          4" << std::endl;
	stream << "#define USCXML_CTX_DEQUEUE_EXTERNAL  5" << std::endl;
	stream << std::endl;

	stream << "#define USCXML_TRANS_SPONTANEOUS     0" << std::endl;
	stream << "#define USCXML_TRANS_TARGETLESS      1" << std::endl;
	stream << "#define USCXML_TRANS_INTERNAL        2" << std::endl;
	stream << "#define USCXML_TRANS_HISTORY         3" << std::endl;
	stream << "#define USCXML_TRANS_INITIAL         4" << std::endl;
	stream << std::endl;

	stream << "#define USCXML_STATE_ATOMIC          0" << std::endl;
	stream << "#define USCXML_STATE_PARALLEL        1" << std::endl;
	stream << "#define USCXML_STATE_COMPOUND        2" << std::endl;
	stream << "#define USCXML_STATE_FINAL           3" << std::endl;
	stream << "#define USCXML_STATE_HISTORY_DEEP    4" << std::endl;
	stream << "#define USCXML_STATE_HISTORY_SHALLOW 5" << std::endl;
	stream << "#define USCXML_STATE_INITIAL         6" << std::endl;
	stream << "#define USCXML_STATE_HAS_HISTORY     7" << std::endl;
	stream << std::endl;

	stream << "#define USCXML_ERR_OK                0" << std::endl;
	stream << "#define USCXML_ERR_DONE              1" << std::endl;
	stream << std::endl;

	stream << "#define USCXML_EVENT_SPONTANEOUS     0" << std::endl;
	stream << std::endl;
	stream << "#define TRACE_EXECUTION              1" << std::endl;
	stream << std::endl;

}

void ChartToPromela::writeCommonTypeDefs(std::ostream& stream) {
	stream << "/* common type definitions */" << std::endl;
	PromelaCodeAnalyzer::PromelaTypedef typeDefs = _analyzer->getTypes();
	if (typeDefs.types.size() == 0)
		return;

	std::list<PromelaCodeAnalyzer::PromelaTypedef> individualDefs;
	std::list<PromelaCodeAnalyzer::PromelaTypedef> currDefs;
	currDefs.push_back(typeDefs);

	while(currDefs.size() > 0) {
		if (std::find(individualDefs.begin(), individualDefs.end(), currDefs.front()) == individualDefs.end()) {
			individualDefs.push_back(currDefs.front());
			for (std::map<std::string, PromelaCodeAnalyzer::PromelaTypedef>::iterator typeIter = currDefs.front().types.begin(); typeIter != currDefs.front().types.end(); typeIter++) {
				currDefs.push_back(typeIter->second);
			}
		}
		currDefs.pop_front();
	}
	individualDefs.pop_front();

	for (std::list<PromelaCodeAnalyzer::PromelaTypedef>::reverse_iterator rIter = individualDefs.rbegin(); rIter != individualDefs.rend(); rIter++) {
		PromelaCodeAnalyzer::PromelaTypedef currDef = *rIter;

		if (currDef.types.size() == 0 || currDef.name.size() == 0)
			continue;

		stream << "typedef " << currDef.name << " {" << std::endl;
		if (currDef.name.compare("_event_t") ==0) {
			if (_analyzer->usesEventField("delay")) {
				// make sure delay is the first member for sorted enqueuing to work
				stream << "  " << declForRange("delay", 0, _analyzer->largestDelay, true) << ";" << std::endl;
#if NEW_DELAY_RESHUFFLE
#else
				stream << "  short seqNr;" << std::endl;
#endif
			}
			stream << "  " << declForRange("name", 0, _analyzer->getTrie().lastIndex, true) << ";" << std::endl;
			if (_analyzer->usesEventField("invokeid")) {
				stream << "  " << declForRange("invokeid", 0, _machinesAll->size() + 1, true) << ";" << std::endl;
			}
			if (_analyzer->usesEventField("origin")) {
				stream << "  " << declForRange("origin", 0, _machinesAll->size() + 1, true) << ";" << std::endl;
			}
		}
		for (std::map<std::string, PromelaCodeAnalyzer::PromelaTypedef>::iterator tIter = currDef.types.begin(); tIter != currDef.types.end(); tIter++) {
			if (currDef.name.compare("_event_t") == 0 && (tIter->first.compare("name") == 0 ||
			        tIter->first.compare("seqNr") == 0 ||
			        tIter->first.compare("invokeid") == 0 ||
			        tIter->first.compare("origin") == 0 ||
			        tIter->first.compare("delay") == 0)) { // special treatment for _event
				continue;
			}
			if (tIter->second.types.size() == 0) {
				stream << "  " << declForRange(tIter->first, tIter->second.minValue, tIter->second.maxValue, true) << ";" << std::endl; // not further nested
				//				stream << "  int " << tIter->first << ";" << std::endl; // not further nested
			} else {
				stream << "  " << tIter->second.name << " " << tIter->first << ";" << std::endl;
			}
		}
		stream << "};" << std::endl << std::endl;
	}

	//	stream << "/* typedef instances */" << std::endl;
	//	PromelaCodeAnalyzer::PromelaTypedef allTypes = _analyzer->getTypes();
	//	std::map<std::string, PromelaCodeAnalyzer::PromelaTypedef>::iterator typeIter = allTypes.types.begin();
	//	while(typeIter != allTypes.types.end()) {
	//		if (typeIter->second.types.size() > 0) {
	//			// an actual typedef
	//			stream << "hidden " << typeIter->second.name << " " << typeIter->first << ";" << std::endl;
	//		} else {
	//			stream << "hidden " << declForRange(typeIter->first, typeIter->second.minValue, typeIter->second.maxValue) << ";" << std::endl;
	//		}
	//		typeIter++;
	//	}

}

void ChartToPromela::writeTypeDefs(std::ostream& stream) {
	stream << "/* custom type definitions for " << _prefix << " */" << std::endl;

}

void ChartToPromela::writeCommonVariables(std::ostream& stream) {
	stream << "hidden int tmpIndex;" << std::endl;
	if (_analyzer->usesComplexEventStruct()) {
		stream << "hidden _event_t tmpE;" << std::endl;
	} else {
		stream << "hidden int tmpE;" << std::endl;
	}

	if (_analyzer->hasIndexLessLoops())
		stream << "hidden int _index;             /* helper for indexless foreach loops */" << std::endl;

	if (_analyzer->usesEventField("sendid"))
		stream << "hidden int _lastSendId = 0;         /* sequential counter for send ids */" << std::endl;

	if (_analyzer->usesEventField("delay"))
		stream << "hidden short _lastSeqId = 0;     /* sequential counter for delayed events */"  << std::endl;
	stream << std::endl;

}

void ChartToPromela::writeVariables(std::ostream& stream) {
	stream << "/* custom definitions and global variables */" << std::endl;
	stream << "bool " << _prefix << "flags[6];" << std::endl;
	stream << "bool " << _prefix << "config[" << _states.size() << "];" << std::endl;
	stream << "bool " << _prefix << "history[" << _states.size() << "];" << std::endl;
	stream << "bool " << _prefix << "invocations[" << _states.size() << "];" << std::endl;
//	stream << "bool " << _prefix << "initialized_data[" << _states.size() << "];" << std::endl;

	size_t tolerance = 6;

	if (_analyzer->usesComplexEventStruct()) {
		// event is defined with the typedefs
		stream << "hidden _event_t " << _prefix << "_event;               /* current event */" << std::endl;
		stream << "hidden _event_t " << _prefix << "_tmpE;          /* temporary event for send */" << std::endl;
		stream << "chan " << _prefix << "iQ   = [" << (std::max)(_internalQueueLength, (size_t)1) << "] of {_event_t}  /* internal queue */" << std::endl;
		stream << "chan " << _prefix << "eQ   = [" << _externalQueueLength + tolerance << "] of {_event_t}  /* external queue */" << std::endl;
		if (_allowEventInterleaving)
			stream << "chan " << _prefix << "tmpQ = [" << (std::max)(_externalQueueLength + tolerance, (size_t)1) << "] of {_event_t}  /* temporary queue for external events in transitions */" << std::endl;
	} else {
		stream << "unsigned " << _prefix << "_event : " << BIT_WIDTH(_analyzer->getLiterals().size() + 1) << ";                /* current event */" << std::endl;
		stream << "hidden unsigned " << _prefix << "_tmpE : " << BIT_WIDTH(_analyzer->getLiterals().size() + 1) << ";         /* temporary event for send */" << std::endl;
		stream << "chan " << _prefix << "iQ   = [" << (std::max)(_internalQueueLength, (size_t)1) << "] of {int}  /* internal queue */" << std::endl;
		stream << "chan " << _prefix << "eQ   = [" << _externalQueueLength + tolerance << "] of {int}  /* external queue */" << std::endl;
		if (_allowEventInterleaving)
			stream << "chan " << _prefix << "tmpQ = [" << (std::max)(_externalQueueLength + tolerance, (size_t)1) << "] of {int}  /* temporary queue for external events in transitions */" << std::endl;
	}

	if (_transitions.size() > 0) {
		stream << std::endl;
		stream << "typedef " << _prefix << "transition_t {" << std::endl;
		stream << "  unsigned source : " << BIT_WIDTH(_states.size()) << ";" << std::endl;
		stream << "  bool target[" << _states.size() << "];" << std::endl;
		stream << "  bool type[5];" << std::endl;
		stream << "  bool conflicts[" << _transitions.size() << "];" << std::endl;
		stream << "  bool exit_set[" << _states.size() << "];" << std::endl;
		stream << "}" << std::endl;
		stream << "hidden " << _prefix << "transition_t " << _prefix << "transitions[" << toStr(_transitions.size()) << "];" << std::endl;
		stream << std::endl;
	}

	if (_states.size() > 0) {
		stream << "typedef " << _prefix << "state_t {" << std::endl;
		stream << "  unsigned parent : " << BIT_WIDTH(_states.size()) << ";" << std::endl;
		stream << "  bool children[" << _states.size() << "];" << std::endl;
		stream << "  bool completion[" << _states.size() << "];" << std::endl;
		stream << "  bool ancestors[" << _states.size() << "];" << std::endl;
		stream << "  bool type[8];" << std::endl;
		stream << "}" << std::endl;
		stream << "hidden " << _prefix << "state_t " << _prefix << "states[" << toStr(_states.size()) << "];" << std::endl;
		stream << std::endl;
	}

	stream << "typedef " << _prefix << "ctx_t {" << std::endl;
	if (_transitions.size() > 0) {
		stream << "  bool conflicts[" << _transitions.size() << "];" << std::endl;
		stream << "  bool trans_set[" << _transitions.size() << "];" << std::endl;
	}

	stream << "  bool target_set[" << _states.size() << "];" << std::endl;
	stream << "  bool exit_set[" << _states.size() << "];" << std::endl;
	stream << "  bool entry_set[" << _states.size() << "];" << std::endl;
	stream << "  bool tmp_states[" << _states.size() << "];" << std::endl;
	stream << "}" << std::endl;
	stream << "hidden " << _prefix << "ctx_t " << _prefix << "ctx;" << std::endl;
	stream << std::endl;
	stream << std::endl;

	std::set<std::string> processedIdentifiers;

	// automatic types
	std::list<DOMElement*> datas = DOMUtils::inDocumentOrder({ XML_PREFIX(_scxml).str() + "data" }, _scxml, false);
	PromelaCodeAnalyzer::PromelaTypedef allTypes = _analyzer->getTypes();

	for (auto data : datas) {
		std::string identifier = (HAS_ATTR_CAST(data, "id") ? ATTR_CAST(data, "id") : "");
		std::string type = boost::trim_copy(HAS_ATTR_CAST(data, "type") ? ATTR_CAST(data, "type") : "");

		_dataModelVars.insert(identifier);
		if (processedIdentifiers.find(identifier) != processedIdentifiers.end())
			continue;

		processedIdentifiers.insert(identifier);

		if (boost::starts_with(type, "string")) {
			type = "int" + type.substr(6, type.length() - 6);
		}

		if (type.length() == 0 || type == "auto") {
			if (allTypes.types.find(identifier) != allTypes.types.end()) {
				type = allTypes.types[identifier].name;
			} else {
				LOGD(USCXML_ERROR) << "Automatic or no type for '" << identifier << "' but no type resolved";
				continue;
			}
		}

		std::string arrSize;
		size_t bracketPos = type.find("[");
		if (bracketPos != std::string::npos) {
			arrSize = type.substr(bracketPos, type.length() - bracketPos);
			type = type.substr(0, bracketPos);
		}
		std::string decl = type + " " + _prefix + identifier + arrSize;
		stream << decl << ";" << std::endl;

	}

	// implicit and dynamic types
	std::map<std::string, PromelaCodeAnalyzer::PromelaTypedef>::iterator typeIter = allTypes.types.begin();
	while(typeIter != allTypes.types.end()) {
		if (typeIter->second.occurrences.find(this) == typeIter->second.occurrences.end()) {
			typeIter++;
			continue;
		}

		if (processedIdentifiers.find(typeIter->first) != processedIdentifiers.end()) {
			typeIter++;
			continue;
		}

		if (typeIter->first == "_event"
		        || typeIter->first == "config"
		        || typeIter->first == "_ioprocessors"
		        || typeIter->first == "_SESSIONID"
		        || typeIter->first == "_NAME"
		        || !std::any_of(typeIter->first.begin(), typeIter->first.end(), ::islower)
		   ) {
			typeIter++;
			continue;
		}

		processedIdentifiers.insert(typeIter->first);

		if (typeIter->second.types.size() == 0) {
			stream << "hidden " << declForRange(_prefix + typeIter->first, typeIter->second.minValue, typeIter->second.maxValue) << ";" << std::endl;
		} else {
			stream << "hidden " << _prefix << typeIter->second.name << " " << typeIter->first << ";" << std::endl;
		}
		typeIter++;
	}

	if (_analyzer->getTypes().types.find("_ioprocessors") != _analyzer->getTypes().types.end()) {
		stream << "hidden _ioprocessors_t " << _prefix << "_ioprocessors;" << std::endl;
		_varInitializers.push_front("_ioprocessors.scxml.location = " + (_invokerid.size() > 0 ? _analyzer->macroForLiteral(_invokerid) : "1") + ";");
	}

	stream << "hidden int " << _prefix << "procid;             /* the process id running this machine */" << std::endl;

}


void ChartToPromela::writeStrings(std::ostream& stream) {
	stream << "/* states, events and string literals */" << std::endl;
	std::set<std::string> literals = _analyzer->getLiterals();

	{
		for (size_t i = 0; i < _states.size(); i++) {
			if (HAS_ATTR(_states[i], "id")) {
				stream << "#define " << _prefix << _analyzer->macroForLiteral(ATTR(_states[i], "id")) << " " << toStr(i);
				stream << " /* index for state " << ATTR(_states[i], "id") << " */" << std::endl;
			}
		}
	}

	{
		size_t i = 0;
		for (auto machine : *_machinesAll) {
			i++;
			stream << "#define " << _analyzer->macroForLiteral(machine.second->_invokerid) << " " << toStr(i);
			stream << " /* index for invoker " << machine.second->_invokerid << " */" << std::endl;
		}
	}

	for (auto literal : literals) {
		stream << "#define " << _analyzer->macroForLiteral(literal) << " " << _analyzer->indexForLiteral(literal) << " /* " << literal << " */" << std::endl;
	}
}

void ChartToPromela::writeTransitions(std::ostream& stream) {
	for (size_t i = 0; i < _transitions.size(); i++) {
		DOMElement* transition(_transitions[i]);

		/** source */
		stream << "  " << _prefix << "transitions[" << toStr(i) << "].source = ";
		stream << ATTR_CAST(transition->getParentNode(), "documentOrder") ;
		stream << ";" << std::endl;

		/** target */
		if (HAS_ATTR(transition, "targetBools")) {
			std::string targetBools = ATTR(transition, "targetBools");
			for (size_t j = 0; j < _states.size(); j++) {
				if (targetBools[j] == '1')
					stream << "  " << _prefix << "transitions[" << toStr(i) << "].target[" << toStr(j) << "] = 1;" << std::endl;
			}
		}

		if (!HAS_ATTR(transition, "event"))
			stream << "  " << _prefix << "transitions[" << toStr(i) << "].type[USCXML_TRANS_SPONTANEOUS] = 1;" << std::endl;

		if (!HAS_ATTR(transition, "target"))
			stream << "  " << _prefix << "transitions[" << toStr(i) << "].type[USCXML_TRANS_TARGETLESS] = 1;" << std::endl;

		if (HAS_ATTR(transition, "type") && ATTR(transition, "type") == "internal")
			stream << "  " << _prefix << "transitions[" << toStr(i) << "].type[USCXML_TRANS_INTERNAL] = 1;" << std::endl;

		if (TAGNAME_CAST(transition->getParentNode()) == XML_PREFIX(transition).str() + "history")
			stream << "  " << _prefix << "transitions[" << toStr(i) << "].type[USCXML_TRANS_HISTORY] = 1;" << std::endl;

		if (TAGNAME_CAST(transition->getParentNode()) == XML_PREFIX(transition).str() + "initial")
			stream << "  " << _prefix << "transitions[" << toStr(i) << "].type[USCXML_TRANS_INITIAL] = 1;" << std::endl;

		if (HAS_ATTR(transition, "conflictBools")) {
			std::string conflicts = ATTR(transition, "conflictBools");
			for (auto j = 0; j < conflicts.size(); j++) {
				if (conflicts[j] == '1')
					stream << "  " << _prefix << "transitions[" << toStr(i) << "].conflicts[" << toStr(j) << "] = 1;" << std::endl;
			}
		}

		if (HAS_ATTR(transition, "exitSetBools")) {
			std::string exitSet = ATTR(transition, "exitSetBools");
			for (auto j = 0; j < exitSet.size(); j++) {
				if (exitSet[j] == '1')
					stream << "  " << _prefix << "transitions[" << toStr(i) << "].exit_set[" << toStr(j) << "] = 1;" << std::endl;
			}
		}

		stream << std::endl;

	}
}



void ChartToPromela::writeStates(std::ostream& stream) {
	for (size_t i = 0; i < _states.size(); i++) {
		DOMElement* state(_states[i]);

		stream << "  " << _prefix << "states[" << toStr(i) << "].parent = ";
		stream << (i == 0 ? "0" : ATTR_CAST(state->getParentNode(), "documentOrder"));
		stream << ";" << std::endl;


		if (HAS_ATTR(state, "childBools")) {
			std::string childs = ATTR(state, "childBools");
			for (auto j = 0; j < childs.size(); j++) {
				if (childs[j] == '1')
					stream << "  " << _prefix << "states[" << toStr(i) << "].children[" << toStr(j) << "] = 1;" << std::endl;
			}
		}

		if (HAS_ATTR(state, "completionBools")) {
			std::string completions = ATTR(state, "completionBools");
			for (auto j = 0; j < completions.size(); j++) {
				if (completions[j] == '1')
					stream << "  " << _prefix << "states[" << toStr(i) << "].completion[" << toStr(j) << "] = 1;" << std::endl;
			}
		}

		if (HAS_ATTR(state, "ancBools")) {
			std::string ancestors = ATTR(state, "ancBools");
			for (auto j = 0; j < ancestors.size(); j++) {
				if (ancestors[j] == '1')
					stream << "  " << _prefix << "states[" << toStr(i) << "].ancestors[" << toStr(j) << "] = 1;" << std::endl;
			}
		}
		if (false) {
		} else if (iequals(TAGNAME(state), "initial")) {
			stream << "  " << _prefix << "states[" << toStr(i) << "].type[USCXML_STATE_INITIAL] = 1;" << std::endl;
		} else if (isFinal(state)) {
			stream << "  " << _prefix << "states[" << toStr(i) << "].type[USCXML_STATE_FINAL] = 1;" << std::endl;
		} else if (isHistory(state)) {
			if (HAS_ATTR(state, "type") && iequals(ATTR(state, "type"), "deep")) {
				stream << "  " << _prefix << "states[" << toStr(i) << "].type[USCXML_STATE_HISTORY_DEEP] = 1;" << std::endl;
			} else {
				stream << "  " << _prefix << "states[" << toStr(i) << "].type[USCXML_STATE_HISTORY_SHALLOW] = 1;" << std::endl;
			}
		} else if (isAtomic(state)) {
			stream << "  " << _prefix << "states[" << toStr(i) << "].type[USCXML_STATE_ATOMIC] = 1;" << std::endl;
		} else if (isParallel(state)) {
			stream << "  " << _prefix << "states[" << toStr(i) << "].type[USCXML_STATE_PARALLEL] = 1;" << std::endl;
		} else if (isCompound(state)) {
			stream << "  " << _prefix << "states[" << toStr(i) << "].type[USCXML_STATE_COMPOUND] = 1;" << std::endl;
		} else { // <scxml>
			stream << "  " << _prefix << "states[" << toStr(i) << "].type[USCXML_STATE_COMPOUND] = 1;" << std::endl;
		}
		if (HAS_ATTR(state, "hasHistoryChild")) {
			stream << "  " << _prefix << "states[" << toStr(i) << "].type[USCXML_STATE_HAS_HISTORY] = 1;" << std::endl;
		}

		stream << std::endl;

	}
}

void ChartToPromela::writeRaiseDoneDate(std::ostream& stream, const DOMElement* donedata, size_t indent) {
	std::string padding;
	for (size_t i = 0; i < indent; i++) {
		padding += "  ";
	}

	std::list<DOMElement*> contents = DOMUtils::filterChildElements(XML_PREFIX(donedata).str() + "content", donedata);
	if (contents.size() > 0) {
		auto& content = contents.front();

		// an expression
		if (HAS_ATTR(content, "expr")) {
			stream << dataToAssignments(_prefix + "_tmpE.data", Data(ADAPT_SRC(ATTR(content, "expr")), Data::INTERPRETED));
			return;
		}

		std::list<DOMNode*> textChilds = DOMUtils::filterChildType(DOMNode::TEXT_NODE, content);
		std::stringstream ss;
		for (auto text : textChilds) {
			ss << X(text->getNodeValue()).str();
		}

		// text childs
		std::string value = boost::trim_copy(ss.str());
		if (value.size() > 0) {
			Data d = Data::fromJSON(value);
			if (!d.empty()) {
				stream << dataToAssignments(_prefix + "_tmpE.data", d);
			} else {
				if (!isNumeric(value.c_str(), 10)) {
					stream << dataToAssignments(_prefix + "_tmpE.data", Data(value, Data::VERBATIM));
				} else {
					stream << dataToAssignments(_prefix + "_tmpE.data", Data(value, Data::INTERPRETED));
				}
			}
			return;
		}
	}

	std::list<DOMElement*> params = DOMUtils::filterChildElements(XML_PREFIX(donedata).str() + "param", donedata);
	if (params.size() > 0) {
		Data d;
		for (auto& param : params) {
			if (!HAS_ATTR(param, "name"))
				continue;
			std::string name = ATTR(param, "name");
			std::string expr;
			if (HAS_ATTR(param, "expr")) {
				expr = ATTR(param, "expr");
			} else if (HAS_ATTR(param, "location")) {
				expr = ATTR(param, "location");
			}

			d[name] = Data(expr, Data::INTERPRETED);
		}
		stream << dataToAssignments(_prefix + "_tmpE.data", d);

	}

}

void ChartToPromela::writeExecContent(std::ostream& stream, const XERCESC_NS::DOMNode* node, size_t indent) {
	if (!node)
		return;

	std::string padding;
	for (size_t i = 0; i < indent; i++) {
		padding += "  ";
	}

	if (node->getNodeType() == DOMNode::TEXT_NODE) {
		if (boost::trim_copy(X(node->getNodeValue()).str()).length() > 0)
			stream << beautifyIndentation(ADAPT_SRC(X(node->getNodeValue()).str()), indent) << std::endl;
	}

	if (node->getNodeType() != DOMNode::ELEMENT_NODE)
		return; // skip anything not an element

	const XERCESC_NS::DOMElement* element = static_cast<const XERCESC_NS::DOMElement*>(node);

	if (false) {
	} else if(TAGNAME(element) == "onentry" ||
	          TAGNAME(element) == "onexit" ||
	          TAGNAME(element) == "transition" ||
	          TAGNAME(element) == "finalize") {
		// descent into childs and write their contents
		const XERCESC_NS::DOMNode* child = node->getFirstChild();
		while(child) {
			writeExecContent(stream, child, indent);
			child = child->getNextSibling();
		}
	} else if(TAGNAME(element) == "script") {
		std::list<DOMNode*> scriptTexts = DOMUtils::filterChildType(DOMNode::TEXT_NODE, node, true);
		for (auto scriptText : scriptTexts) {
			stream << ADAPT_SRC(beautifyIndentation(X(scriptText->getNodeValue()).str(), indent)) << std::endl;
		}

	} else if(TAGNAME(element) == "log") {
		std::string label = (HAS_ATTR(element, "label") ? ATTR(element, "label") : "");
		std::string expr = (HAS_ATTR(element, "expr") ? ADAPT_SRC(ATTR(element, "expr")) : "");
		std::string trimmedExpr = boost::trim_copy(expr);
		bool isStringLiteral = (boost::starts_with(trimmedExpr, "\"") || boost::starts_with(trimmedExpr, "'"));

		std::string formatString;
		std::string varString;
		std::string seperator;

		if (label.size() > 0) {
			if (expr.size() > 0) {
				formatString += label + ": ";
			} else {
				formatString += label;
			}
		}

		if (isStringLiteral) {
			formatString += expr;
		} else if (expr.size() > 0) {
			formatString += "%d";
			varString += seperator + expr;
		}

		if (varString.length() > 0) {
			stream << padding << "printf(\"" + formatString + "\", " + varString + ");" << std::endl;
		} else {
			stream << padding << "printf(\"" + formatString + "\");" << std::endl;
		}

	} else if(TAGNAME(element) == "foreach") {
		stream << padding << "for (" << (HAS_ATTR(element, "index") ? _prefix + ATTR(element, "index") : "_index") << " in " << _prefix << ATTR(element, "array") << ") {" << std::endl;
		if (HAS_ATTR(element, "item")) {
			stream << padding << "  " << _prefix << ATTR(element, "item") << " = " << _prefix << ATTR(element, "array") << "[" << (HAS_ATTR(element, "index") ? _prefix + ATTR(element, "index") : "_index") << "];" << std::endl;
		}
		const XERCESC_NS::DOMNode* child = element->getFirstChild();
		while(child) {
			writeExecContent(stream, child, indent + 1);
			child = child->getNextSibling();
		}
		//		if (HAS_ATTR(nodeElem, "index"))
		//			stream << padding << "  " << _prefix << ATTR(nodeElem, "index") << "++;" << std::endl;
		stream << padding << "}" << std::endl;

	} else if(TAGNAME(element) == "if") {
		std::list<DOMElement*> condChain;
		condChain.push_back(const_cast<DOMElement*>(element));

		condChain.splice(condChain.end(), DOMUtils::filterChildElements(XML_PREFIX(element).str() + "elseif", element));
		condChain.splice(condChain.end(), DOMUtils::filterChildElements(XML_PREFIX(element).str() + "else", element));

		writeIfBlock(stream, condChain, indent);

	} else if(TAGNAME(element) == "assign") {

		std::list<DOMNode*> assignTexts = DOMUtils::filterChildType(DOMNode::TEXT_NODE, element, true);
		assert(assignTexts.size() > 0);
		stream << beautifyIndentation(ADAPT_SRC(boost::trim_copy(X(assignTexts.front()->getNodeValue()).str())), indent + 1) << std::endl;

	} else if(TAGNAME(element) == "send" || TAGNAME(element) == "raise") {
		std::string targetQueue;

		stream << padding << "if" << std::endl;
		stream << padding << ":: !" << _prefix << "flags[USCXML_CTX_FINISHED] || " << _prefix << "flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {" << std::endl;

		padding += "  ";
		std::string insertOp = "!";
		if (TAGNAME(element) == "raise") {
			targetQueue = _prefix + "iQ";
		} else if (!HAS_ATTR(element, "target")) {
//      if (_allowEventInterleaving) {
//        targetQueue = _prefix + "tmpQ";
//      } else {
			targetQueue = _prefix + "eQ";
//      }
		} else if (ATTR(element, "target").compare("#_internal") == 0) {
			targetQueue = _prefix + "iQ";
		} else if (ATTR(element, "target").compare("#_parent") == 0) {
			targetQueue = _parent->_prefix + "eQ";
		} else if (boost::starts_with(ATTR(element, "target"), "#_") && _machinesAllPerId->find(ATTR(element, "target").substr(2)) != _machinesAllPerId->end()) {
			targetQueue = (*_machinesAll)[(*_machinesAllPerId)[ATTR(element, "target").substr(2)]]->_prefix + "eQ";
		}
		if (targetQueue.length() > 0) {
			// this is for our external queue
			std::string event;

			if (HAS_ATTR(element, "event")) {
				event = _analyzer->macroForLiteral(ATTR(element, "event"));
			} else if (HAS_ATTR(element, "eventexpr")) {
				event = ADAPT_SRC(ATTR(element, "eventexpr"));
			}
			if (_analyzer->usesComplexEventStruct()) {
				stream << padding << "{" << std::endl;
				std::string typeReset = _analyzer->getTypeReset(_prefix + "_tmpE", _analyzer->getType("_event"), indent + 2);
				std::stringstream typeAssignSS;
				typeAssignSS << padding << "  " << _prefix << "_tmpE.name = " << event << ";" << std::endl;

				if (HAS_ATTR(element, "idlocation")) {
					typeAssignSS << padding << "  /* idlocation */" << std::endl;
					typeAssignSS << padding << "  _lastSendId = _lastSendId + 1;" << std::endl;
					typeAssignSS << padding << "  " << _prefix << ATTR(element, "idlocation") << " = _lastSendId;" << std::endl;
					typeAssignSS << padding << "  " << _prefix << "_tmpE.sendid = _lastSendId;" << std::endl;
					typeAssignSS << padding << "  if" << std::endl;
					typeAssignSS << padding << "  :: _lastSendId == 2147483647 -> _lastSendId = 0;" << std::endl;
					typeAssignSS << padding << "  :: else -> skip;" << std::endl;
					typeAssignSS << padding << "  fi;" << std::endl;
				} else if (HAS_ATTR(element, "id")) {
					typeAssignSS << padding << "  " << _prefix << "_tmpE.sendid = " << _analyzer->macroForLiteral(ATTR(element, "id")) << ";" << std::endl;
				}

				if (_analyzer->usesEventField("invokeid") && _parent != NULL) { // do not send invokeid if we send / raise to ourself
					typeAssignSS << padding << "  " << _prefix << "_tmpE.invokeid = " << _analyzer->macroForLiteral(_invokerid) << ";" << std::endl;
				}

				if (_analyzer->usesEventField("origintype") && !boost::ends_with(targetQueue, "iQ")) {
					typeAssignSS << padding << "  " << _prefix << "_tmpE.origintype = " << _analyzer->macroForLiteral("http://www.w3.org/TR/scxml/#SCXMLEventProcessor") << ";" << std::endl;
				}

				if (_analyzer->usesEventField("origin") && !boost::ends_with(targetQueue, "iQ")) {
					typeAssignSS << padding << "  " << _prefix << "_tmpE.origin = " << _analyzer->macroForLiteral(_invokerid) << ";" << std::endl;
				}

				if (_analyzer->usesEventField("delay")) {
#if NEW_DELAY_RESHUFFLE
#else
//					insertOp += "!";
					typeAssignSS << padding << "  _lastSeqId = _lastSeqId + 1;" << std::endl;
#endif
					if (HAS_ATTR_CAST(element, "delay")) {
						typeAssignSS << padding << "  " << _prefix << "_tmpE.delay = " << ATTR_CAST(element, "delay") << ";" << std::endl;
					} else if (HAS_ATTR_CAST(element, "delayexpr")) {
						typeAssignSS << padding << "  " << _prefix << "_tmpE.delay = " << ADAPT_SRC(ATTR_CAST(element, "delayexpr")) << ";" << std::endl;
					} else {
						typeAssignSS << padding << "  " << _prefix << "_tmpE.delay = 0;" << std::endl;
					}
#if NEW_DELAY_RESHUFFLE
#else
					typeAssignSS << padding << "  " << _prefix << "_tmpE.seqNr = _lastSeqId;" << std::endl;
#endif
				}

				if (_analyzer->usesEventField("type")) {
					std::string eventType = (targetQueue.compare("iQ!") == 0 ? _analyzer->macroForLiteral("internal") : _analyzer->macroForLiteral("external"));
					typeAssignSS << padding << "  " << _prefix << "_tmpE.type = " << eventType << ";" << std::endl;
				}

				std::list<DOMElement*> sendParams = DOMUtils::filterChildElements(XML_PREFIX(element).str() + "param", element);
				std::list<DOMElement*> sendContents = DOMUtils::filterChildElements(XML_PREFIX(element).str() + "content", element);
				std::string sendNameList = ATTR(element, "namelist");
				if (sendParams.size() > 0) {
					for (auto sendParam : sendParams) {
						typeAssignSS << padding << "  " << _prefix << "_tmpE.data." << ATTR(sendParam, "name") << " = " << ADAPT_SRC(ATTR(sendParam, "expr"))  << ";" << std::endl;
					}
				}
				if (sendNameList.size() > 0) {
					std::list<std::string> nameListIds = tokenize(sendNameList);
					std::list<std::string>::iterator nameIter = nameListIds.begin();
					while(nameIter != nameListIds.end()) {
						typeAssignSS << padding << "  " << _prefix << "_tmpE.data." << *nameIter << " = " << ADAPT_SRC(*nameIter) << ";" << std::endl;
						nameIter++;
					}
				}

				if (sendParams.size() == 0 && sendNameList.size() == 0 && sendContents.size() > 0) {
					DOMElement* contentElem = sendContents.front();
					if (contentElem->hasChildNodes() && contentElem->getFirstChild()->getNodeType() == DOMNode::TEXT_NODE) {
						std::string content = spaceNormalize(X(contentElem->getFirstChild()->getNodeValue()).str());
						if (!isNumeric(content.c_str(), 10)) {
							typeAssignSS << padding << "  " << _prefix << "_tmpE.data = " << _analyzer->macroForLiteral(content) << ";" << std::endl;
						} else {
							typeAssignSS << padding << "  " << _prefix << "_tmpE.data = " << content << ";" << std::endl;
						}
					} else if (HAS_ATTR(contentElem, "expr")) {
						typeAssignSS << padding << "  " << _prefix << "_tmpE.data = " << ADAPT_SRC(ATTR(contentElem, "expr")) << ";" << std::endl;
					}
				}

				// remove all fields from typeReset that are indeed set by typeAssign
				//        for (std::string assigned; std::getline(typeAssignSS, assigned); ) {
				//          assigned = assigned.substr(0, assigned.find('='));
				//          assigned = assigned.substr(assigned.find('.'));
				//          std::istringstream typeResetSS (typeReset);
				//          for (std::string reset; std::getline(typeResetSS, reset); ) {
				//            if (!boost::find_first(reset, assigned)) {
				//              stream << reset << std::endl;
				//            }
				//          }
				//        }
				//        stream << typeAssignSS.str();

				std::istringstream typeResetSS (typeReset);
				for (std::string reset; std::getline(typeResetSS, reset); ) {
					std::string resetField = reset.substr(0, reset.find('='));
					resetField = resetField.substr(resetField.find('.'));
					for (std::string assigned; std::getline(typeAssignSS, assigned); ) {
						if (boost::find_first(resetField, assigned)) {
							break;
						}
					}
					stream << reset << std::endl;
				}
				stream << typeAssignSS.str();

				stream << "#if TRACE_EXECUTION" << std::endl;
				if (_analyzer->usesComplexEventStruct()) {
					stream << "printf(\"%d: Sending " << event << " (%d) to " << targetQueue << "\\n\", _pid, " << _prefix << TMP_EVENT_NAME << " );" << std::endl;
				} else {
					stream << "printf(\"Sending " << event << " (%d) to " << targetQueue << "\\n\", " << _prefix << TMP_EVENT_NAME << " );" << std::endl;
				}
				stream << "#endif" << std::endl;
				stream << std::endl;

				stream << padding << "  " << targetQueue << insertOp << _prefix <<"_tmpE;" << std::endl;

				if (_analyzer->usesEventField("delay") && !boost::ends_with(targetQueue, "iQ")) {
					stream << padding << "  insertWithDelay(" << targetQueue << ");" << std::endl;
				}

				stream << padding << "}" << std::endl;
			} else {
				stream << padding << targetQueue << insertOp << event << ";" << std::endl;
			}
		}
		stream << padding << "skip;" << std::endl;

		padding = padding.substr(0, padding.size() - 2);
		stream << padding << "}" << std::endl;
		stream << padding << ":: else -> skip;" << std::endl;
		stream << padding << "fi" << std::endl;

	} else if(TAGNAME(element) == "cancel") {
		if (HAS_ATTR(element, "sendid")) {
			stream << "  " << padding << "cancelSendId(" << _analyzer->macroForLiteral(ATTR(element, "sendid")) << "," << _analyzer->macroForLiteral(_invokerid) << ");" << std::endl;
		} else if (HAS_ATTR(element, "sendidexpr")) {
			stream << "  " << padding << "cancelSendId(" << ADAPT_SRC(ATTR(element, "sendidexpr")) << "," << _analyzer->macroForLiteral(_invokerid) << ");" << std::endl;
		}
	} else {
		std::cerr << "'" << TAGNAME(element) << "' not supported" << std::endl << element << std::endl;
		assert(false);
	}
}



void ChartToPromela::writeFSM(std::ostream& stream) {
	stream << "/* machine microstep function */" << std::endl;
	stream << "#define " << _prefix << "USCXML_NUMBER_STATES " << _states.size() << std::endl;
	stream << "#define " << _prefix << "USCXML_NUMBER_TRANS " << _transitions.size() << std::endl;
	stream << std::endl;

	stream << "proctype " << _prefix << "step() { atomic {" << std::endl;
	stream << std::endl;
	stream << _prefix << "procid = _pid;" << std::endl;

	size_t largestBitWidth = (_states.size() > _transitions.size() ?
	                          BIT_WIDTH(_states.size() + 1) :
	                          BIT_WIDTH(_transitions.size() + 1));

	stream << "unsigned";
	stream << " i : " <<  largestBitWidth << ", ";
	stream << " j : " <<  largestBitWidth << ", ";
	stream << " k : " <<  largestBitWidth << ";" << std::endl;
	stream << std::endl;

	std::list<DOMElement*> globalScripts = DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "script", _scxml, false);
	if (globalScripts.size() > 0) {
		stream << "/* run global scripts */" << std::endl;
		stream << "d_step { " << std::endl;

		for (auto globalScript : globalScripts) {
			TRACE_EXECUTION("Processing executable content for global script");

			writeExecContent(stream, globalScript, 2);
		}
		stream << "} /* d_step */" << std::endl;
		stream << std::endl;
	}

	stream << std::endl;
	stream << "/* ---------------------------- */" << std::endl;
	stream << _prefix << "MICROSTEP:" << std::endl;

	stream << "do" << std::endl;
	stream << ":: !" << _prefix << "flags[USCXML_CTX_FINISHED] -> {" << std::endl;
	stream << "  /* Run until machine is finished */" << std::endl;
	stream << std::endl;

	TRACE_EXECUTION("Taking a step");


#if 0
	writeFSMRescheduleMachines(stream);
	stream << std::endl;
	writeFSMMacrostep(stream);
	stream << std::endl;
	writeFSMDequeueInternalOrSpontaneousEvent(stream);
#else
	writeFSMDequeueEvent(stream);
#endif
	stream << std::endl;
	stream << "d_step { skip;" << std::endl;

	stream << std::endl;
	writeFSMSelectTransitions(stream);
	stream << std::endl;


	stream << "  if" << std::endl;
	stream << "  :: " << _prefix << "flags[USCXML_CTX_TRANSITION_FOUND] -> {" << std::endl;
	stream << "    /* only process anything if we found transitions or are on initial entry */" << std::endl;

	writeFSMRememberHistory(stream);
	stream << std::endl;
	writeFSMEstablishEntrySet(stream);
	stream << std::endl;
	writeFSMExitStates(stream);
	stream << std::endl;
	writeFSMTakeTransitions(stream);
	stream << std::endl;
	writeFSMEnterStates(stream);
	stream << std::endl;

//    TRACE_EXECUTION("Exited States")


	stream << "  }" << std::endl;
	stream << "  :: else -> skip;" << std::endl;
	stream << "  fi /* USCXML_CTX_TRANSITION_FOUND */" << std::endl;
	stream << "  } skip; /* d_step */" << std::endl;

	stream << "} /* !USCXML_CTX_FINISHED */" << std::endl;
	stream << ":: else -> break;" << std::endl;
	stream << "od" << std::endl;
	stream << std::endl;

	writeFSMTerminateMachine(stream);
	stream << std::endl;

	TRACE_EXECUTION("Done");


	stream << "} } /* atomic, step() */" << std::endl;
	stream << std::endl;

}

#if 0
void ChartToPromela::writeFSMRescheduleMachines(std::ostream& stream) {
	if (_analyzer->usesEventField("delay") && _machinesAll->size() > 1) {
		stream << "  /* Determine machines with smallest delay and set their process priority */" << std::endl;
		stream << "  scheduleMachines();" << std::endl << std::endl;
		stream << std::endl;

		stream << "  /* we may return to find ourselves terminated */" << std::endl;
		stream << "  if" << std::endl;
		stream << "  :: " << _prefix << "flags[USCXML_CTX_FINISHED] -> {" << std::endl;
		stream << "    goto " << _prefix << "TERMINATE_MACHINE;" << std::endl;
		stream << "  }" << std::endl;
		stream << "  :: else -> skip;" << std::endl;
		stream << "  fi" << std::endl;
		stream << std::endl;
	}
}

void ChartToPromela::writeFSMMacrostep(std::ostream& stream) {

	stream << "  /* Dequeue an external event */" << std::endl;
	stream << "  " << _prefix << "flags[USCXML_CTX_DEQUEUED_EXTERNAL] = false;" << std::endl;

	stream << "  if" << std::endl;
	stream << "  :: !" << _prefix << "flags[USCXML_CTX_SPONTANEOUS] && len(" << _prefix << "iQ) == 0 -> {" << std::endl;

	stream << "    /* manage invocations */" << std::endl;
	stream << "    i = 0;" << std::endl;
	stream << "    do" << std::endl;
	stream << "    :: i < " << _prefix << "USCXML_NUMBER_STATES -> {" << std::endl;
	stream << "      /* uninvoke */" << std::endl;
	stream << "      if" << std::endl;
	stream << "      :: !" << _prefix << "config[i] && " << _prefix << "invocations[i] -> {" << std::endl;

	TRACE_EXECUTION_V("Uninvoking in state %d", "i");

	stream << "        if" << std::endl;

	for (size_t i = 0; i < _states.size(); i++) {
		std::list<DOMElement*> invokers = DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "invoke" , _states[i]);
		if (invokers.size() > 0) {
			stream << "        :: i == " << toStr(i) << " -> {" << std::endl;
			for (auto invokeElem : invokers) {
				if (_machinesNested.find(invokeElem) == _machinesNested.end())
					continue;
				ChartToPromela* invoker = _machinesNested[invokeElem];
				stream << "          " << invoker->_prefix << "flags[USCXML_CTX_FINISHED] = true;" << std::endl;
			}
			stream << "        }" << std::endl;
		}
	}
	stream << "        :: else -> skip;" << std::endl;
	stream << "        fi" << std::endl;

	stream << "        " << _prefix << "invocations[i] = false;" << std::endl;

	stream << "        skip;" << std::endl;
	stream << "      }" << std::endl;
	stream << "      :: else -> skip;" << std::endl;
	stream << "      fi;" << std::endl;
	stream << std::endl;

	stream << "      /* invoke */" << std::endl;
	stream << "      if" << std::endl;
	stream << "      :: " << _prefix << "config[i] && !" << _prefix << "invocations[i] -> {" << std::endl;
	stream << "        if" << std::endl;

	for (size_t i = 0; i < _states.size(); i++) {
		std::list<DOMElement*> invokers = DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "invoke" , _states[i]);
		if (invokers.size() > 0) {
			stream << "      :: i == " << toStr(i) << " -> {" << std::endl;
			for (auto invokeElem : invokers) {
				if (_machinesNested.find(invokeElem) == _machinesNested.end())
					continue;
				ChartToPromela* invoker = _machinesNested[invokeElem];

				// pass variables via namelist
				if (HAS_ATTR(invokeElem, "namelist")) {
					std::list<std::string> namelist = tokenize(ATTR_CAST(invokeElem, "namelist"));
					for (auto name : namelist) {
						if (invoker->_dataModelVars.find(name) != invoker->_dataModelVars.end()) {
							stream << "          " << invoker->_prefix << name << " = " << _prefix << name << ";" << std::endl;
						}
					}
				}

				// pass variables via params
				std::list<DOMElement*> invokeParams = DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + + "param", invokeElem);
				for (auto param : invokeParams) {
					std::string name = ATTR(param, "name");
					std::string expression = ATTR(param, "expr");
					if (invoker->_dataModelVars.find(name) != invoker->_dataModelVars.end()) {
						stream << "          " << invoker->_prefix << name << " = " << ADAPT_SRC(expression) << ";" << std::endl;
					}
				}

				TRACE_EXECUTION_V("Invoking in state %d", "i");

				stream << "          run " << invoker->_prefix << "step() priority 20;" << std::endl;
				if (HAS_ATTR(invokeElem, "idlocation")) {
					stream << "          " << ADAPT_SRC(ATTR(invokeElem, "idlocation")) << " = ";
					stream << _analyzer->macroForLiteral(invoker->_invokerid) << ";" << std::endl;
				}

			}
			stream << "          " << _prefix << "invocations[i] = true;" << std::endl;
			stream << "          skip;" << std::endl;
			stream << "        }" << std::endl;
		}
	}

	stream << "        :: else -> skip;" << std::endl;
	stream << "        fi" << std::endl;
	stream << "      }" << std::endl;
	stream << "      :: else -> skip;" << std::endl;
	stream << "      fi;" << std::endl;
	stream << "      i = i + 1;" << std::endl;
	stream << "    }" << std::endl;
	stream << "    :: else -> break;" << std::endl;
	stream << "    od;" << std::endl;
	stream << std::endl;

	stream << "    /* Not sure if this should be before the invocation due to auto-forwarding */" << std::endl;
	stream << "    do" << std::endl;
	stream << "    :: len(" << _prefix << "eQ) != 0 -> {" << std::endl;
	stream << "      " << _prefix << "eQ ? " << _prefix << "_event;" << std::endl;

	if (_machinesNested.size() > 0) {
		stream << std::endl;
		stream << "      /* auto-forward event */" << std::endl;
		stream << "      i = 0;" << std::endl;
		stream << "      do" << std::endl;
		stream << "      :: i < " << _prefix << "USCXML_NUMBER_STATES -> {" << std::endl;
		stream << "        if" << std::endl;

		std::string insertOp = "!";
		if (_analyzer->usesEventField("delay")) {
			//            insertOp += "!";
		}


		for (auto state : _states) {
			std::list<DOMElement*> invokers = DOMUtils::filterChildElements(XML_PREFIX(state).str() + "invoke", state, false);
			if (invokers.size() > 0) {
				stream << "        :: i == " << ATTR(state, "documentOrder") << " && " << _prefix << "invocations[i] -> { " << std::endl;
				for (auto invoker : invokers) {
					assert(_machinesNested.find(invoker) != _machinesNested.end());
					if (HAS_ATTR(invoker, "autoforward") && stringIsTrue(ATTR(invoker, "autoforward"))) {
						stream << "          " << _machinesNested[invoker]->_prefix << "eQ " << insertOp << " " << _prefix << "_event;" << std::endl;
						if (_analyzer->usesEventField("delay")) {
							stream << "          insertWithDelay(" << _machinesNested[invoker]->_prefix << "eQ);" << std::endl;
						}
						TRACE_EXECUTION("Auto forwarded event");
					}
				}
				stream << "        skip;" << std::endl;
				stream << "      }" << std::endl;
			}
		}

		stream << "        :: else -> skip;" << std::endl;
		stream << "        fi" << std::endl;
		stream << "        i = i + 1;" << std::endl;
		stream << "      }" << std::endl;
		stream << "      :: else -> break;" << std::endl;
		stream << "      od" << std::endl;

		stream << std::endl;
		stream << "      /* finalize event */" << std::endl;
		stream << "      if" << std::endl;

		for (auto machine : _machinesNested) {

			stream << "      :: " << _prefix << "_event.invokeid == " << _analyzer->macroForLiteral(machine.second->_invokerid) << " -> {" << std::endl;
			std::list<DOMElement*> finalizers = DOMUtils::filterChildElements(XML_PREFIX(machine.first).str() + "finalize", machine.first, false);

			TRACE_EXECUTION("Finalizing event")

			for (auto finalize : finalizers) {
				writeExecContent(stream, finalize, 4);
			}
			stream << "        skip" << std::endl;
			stream << "      }" << std::endl;
		}
		stream << "      :: else -> skip;" << std::endl;

		stream << "      fi" << std::endl;

	}

	TRACE_EXECUTION("Deqeued an external event");
	stream << "  " << _prefix << "flags[USCXML_CTX_DEQUEUED_EXTERNAL] = true;" << std::endl;
	stream << "      break;" << std::endl;
	stream << "    }" << std::endl;
	//  stream << "  :: else -> quit;" << std::endl;
	stream << "    od;" << std::endl;

	stream << "  }" << std::endl;
	stream << "  :: else -> skip;" << std::endl;
	stream << "  fi" << std::endl;
	stream << std::endl;
}

void ChartToPromela::writeFSMDequeueInternalOrSpontaneousEvent(std::ostream& stream) {
	stream << "  if" << std::endl;
	stream << "  :: !" << _prefix << "flags[USCXML_CTX_DEQUEUED_EXTERNAL] -> {" << std::endl;
	stream << "    /* Try with a spontaneous event or dequeue an internal event */" << std::endl;
	stream << "    if" << std::endl;
	stream << "    :: " << _prefix << "flags[USCXML_CTX_SPONTANEOUS] -> {" << std::endl;
	stream << "      /* We try with a spontaneous event */" << std::endl;
	stream << "      " << _prefix << EVENT_NAME << " = USCXML_EVENT_SPONTANEOUS;" << std::endl;
	stream << "    }" << std::endl;
	stream << "    :: else -> {" << std::endl;
	stream << "      /* We try with an internal event */" << std::endl;
	stream << "      assert(len(" << _prefix << "iQ) > 0);" << std::endl;
	stream << "      " << _prefix << "iQ ? " << _prefix << "_event;" << std::endl;
	stream << "    }" << std::endl;
	stream << "    fi" << std::endl;
	stream << "  }" << std::endl;
	stream << "  :: else -> skip;" << std::endl;
	stream << "  fi" << std::endl;

}
#endif

#if 1
void ChartToPromela::writeFSMDequeueEvent(std::ostream& stream) {
	stream << "  /* Dequeue an event */" << std::endl;
	stream << "  " << _prefix << "flags[USCXML_CTX_DEQUEUE_EXTERNAL] = false;" << std::endl;
	stream << "  if" << std::endl;
	stream << "  ::" << _prefix << "flags[USCXML_CTX_SPONTANEOUS] -> {" << std::endl;
	stream << "    " << _prefix << EVENT_NAME << " = USCXML_EVENT_SPONTANEOUS;" << std::endl;

	TRACE_EXECUTION("Trying with a spontaneous event");

	stream << "  }" << std::endl;
	stream << "  :: else -> {" << std::endl;
	stream << "    if" << std::endl;
	stream << "    :: len(" << _prefix << "iQ) != 0 -> {" << std::endl;
	stream << "      " << _prefix << "iQ ? " << _prefix << "_event;" << std::endl;

	TRACE_EXECUTION("Deqeued an internal event");

	stream << "    }" << std::endl;
	stream << "    :: else -> {" << std::endl;
	stream << "      " << _prefix << "flags[USCXML_CTX_DEQUEUE_EXTERNAL] = true;" << std::endl;
	stream << "    }" << std::endl;
	stream << "    fi;" << std::endl;
	stream << "  }" << std::endl;
	stream << "  fi;" << std::endl;
	stream << std::endl;

	stream << std::endl;

	stream << "  if" << std::endl;
	stream << "  :: " << _prefix << "flags[USCXML_CTX_DEQUEUE_EXTERNAL] -> {" << std::endl;
	stream << "    /* manage invocations */" << std::endl;
	stream << "    i = 0;" << std::endl;
	stream << "    do" << std::endl;
	stream << "    :: i < " << _prefix << "USCXML_NUMBER_STATES -> {" << std::endl;
	stream << "      d_step { " << std::endl;
	stream << "      /* uninvoke */" << std::endl;
	stream << "      if" << std::endl;
	stream << "      :: !" << _prefix << "config[i] && " << _prefix << "invocations[i] -> {" << std::endl;

	TRACE_EXECUTION_V("Uninvoking in state %d", "i");

	stream << "        if" << std::endl;

	for (size_t i = 0; i < _states.size(); i++) {
		std::list<DOMElement*> invokers = DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "invoke" , _states[i]);
		if (invokers.size() > 0) {
			stream << "        :: i == " << toStr(i) << " -> {" << std::endl;
			for (auto invokeElem : invokers) {
				if (_machinesNested.find(invokeElem) == _machinesNested.end())
					continue;
				ChartToPromela* invoker = _machinesNested[invokeElem];
				stream << "          " << invoker->_prefix << "flags[USCXML_CTX_FINISHED] = true;" << std::endl;
			}
			stream << "        }" << std::endl;
		}
	}
	stream << "        :: else -> skip;" << std::endl;
	stream << "        fi" << std::endl;

	stream << "        " << _prefix << "invocations[i] = false;" << std::endl;

	stream << "        skip;" << std::endl;
	stream << "      }" << std::endl;
	stream << "      :: else -> skip;" << std::endl;
	stream << "      fi;" << std::endl;
	stream << "      } /* d_step */" << std::endl;

	stream << std::endl;



	stream << "      /* invoke */" << std::endl;
	stream << "      if" << std::endl;
	stream << "      :: " << _prefix << "config[i] && !" << _prefix << "invocations[i] -> {" << std::endl;
	stream << "        if" << std::endl;

	for (size_t i = 0; i < _states.size(); i++) {
		std::list<DOMElement*> invokers = DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "invoke" , _states[i]);
		if (invokers.size() > 0) {
			stream << "      :: i == " << toStr(i) << " -> {" << std::endl;
			for (auto invokeElem : invokers) {
				if (_machinesNested.find(invokeElem) == _machinesNested.end())
					continue;
				ChartToPromela* invoker = _machinesNested[invokeElem];

				// pass variables via namelist
				if (HAS_ATTR(invokeElem, "namelist")) {
					std::list<std::string> namelist = tokenize(ATTR_CAST(invokeElem, "namelist"));
					for (auto name : namelist) {
						if (invoker->_dataModelVars.find(name) != invoker->_dataModelVars.end()) {
							stream << "          " << invoker->_prefix << name << " = " << _prefix << name << ";" << std::endl;
						}
					}
				}

				// pass variables via params
				std::list<DOMElement*> invokeParams = DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + + "param", invokeElem);
				for (auto param : invokeParams) {
					std::string name = ATTR(param, "name");
					std::string expression = ATTR(param, "expr");
					if (invoker->_dataModelVars.find(name) != invoker->_dataModelVars.end()) {
						stream << "          " << invoker->_prefix << name << " = " << ADAPT_SRC(expression) << ";" << std::endl;
					}
				}

				TRACE_EXECUTION_V("Invoking in state %d", "i");

				stream << "          run " << invoker->_prefix << "step() priority 20;" << std::endl;
				if (HAS_ATTR(invokeElem, "idlocation")) {
					stream << "          " << ADAPT_SRC(ATTR(invokeElem, "idlocation")) << " = ";
					stream << _analyzer->macroForLiteral(invoker->_invokerid) << ";" << std::endl;
				}

			}
			stream << "          " << _prefix << "invocations[i] = true;" << std::endl;
			stream << "          skip;" << std::endl;
			stream << "        }" << std::endl;
		}
	}

	stream << "        :: else -> skip;" << std::endl;
	stream << "        fi" << std::endl;
	stream << "      }" << std::endl;
	stream << "      :: else -> skip;" << std::endl;
	stream << "      fi;" << std::endl;
	stream << "      i = i + 1;" << std::endl;
	stream << "    }" << std::endl;
	stream << "    :: else -> break;" << std::endl;
	stream << "    od;" << std::endl;

	stream << std::endl;

	if (_analyzer->usesEventField("delay") && _machinesAll->size() > 1) {
		stream << "    /* Determine machines with smallest delay and set their process priority */" << std::endl;
		stream << "    scheduleMachines();" << std::endl << std::endl;
	}

	stream << "    /* we may return to find ourselves terminated */" << std::endl;
	stream << "    if" << std::endl;
	stream << "    :: " << _prefix << "flags[USCXML_CTX_FINISHED] -> {" << std::endl;
	stream << "      goto " << _prefix << "TERMINATE_MACHINE;" << std::endl;
	stream << "    }" << std::endl;
	stream << "    :: else -> skip;" << std::endl;
	stream << "    fi" << std::endl;


	stream << "    /* Not sure if this should be before the invocation due to auto-forwarding */" << std::endl;
	stream << "    if" << std::endl;
	stream << "    :: len(" << _prefix << "eQ) != 0 -> {" << std::endl;
	stream << "      " << _prefix << "eQ ? " << _prefix << "_event;" << std::endl;

	if (_machinesNested.size() > 0) {
		stream << std::endl;
		stream << "      d_step {" << std::endl;
		stream << "      /* auto-forward event */" << std::endl;
		stream << "      i = 0;" << std::endl;
		stream << "      do" << std::endl;
		stream << "      :: i < " << _prefix << "USCXML_NUMBER_STATES -> {" << std::endl;
		stream << "        if" << std::endl;

		std::string insertOp = "!";
		if (_analyzer->usesEventField("delay")) {
			//            insertOp += "!";
		}


		for (auto state : _states) {
			std::list<DOMElement*> invokers = DOMUtils::filterChildElements(XML_PREFIX(state).str() + "invoke", state, false);
			if (invokers.size() > 0) {
				stream << "        :: i == " << ATTR(state, "documentOrder") << " && " << _prefix << "invocations[i] -> { " << std::endl;
				for (auto invoker : invokers) {
					assert(_machinesNested.find(invoker) != _machinesNested.end());
					if (HAS_ATTR(invoker, "autoforward") && stringIsTrue(ATTR(invoker, "autoforward"))) {
						stream << "          " << _machinesNested[invoker]->_prefix << "eQ " << insertOp << " " << _prefix << "_event;" << std::endl;
						if (_analyzer->usesEventField("delay")) {
							stream << "          insertWithDelay(" << _machinesNested[invoker]->_prefix << "eQ);" << std::endl;
						}
						TRACE_EXECUTION("Auto forwarded event");
					}
				}
				stream << "        skip;" << std::endl;
				stream << "      }" << std::endl;
			}
		}

		stream << "        :: else -> skip;" << std::endl;
		stream << "        fi" << std::endl;
		stream << "        i = i + 1;" << std::endl;
		stream << "      }" << std::endl;
		stream << "      :: else -> break;" << std::endl;
		stream << "      od" << std::endl;

		stream << std::endl;
		stream << "      /* finalize event */" << std::endl;
		stream << "      if" << std::endl;

		for (auto machine : _machinesNested) {

			stream << "      :: " << _prefix << "_event.invokeid == " << _analyzer->macroForLiteral(machine.second->_invokerid) << " -> {" << std::endl;
			std::list<DOMElement*> finalizers = DOMUtils::filterChildElements(XML_PREFIX(machine.first).str() + "finalize", machine.first, false);

			TRACE_EXECUTION("Finalizing event")

			for (auto finalize : finalizers) {
				writeExecContent(stream, finalize, 4);
			}
			stream << "        skip" << std::endl;
			stream << "      }" << std::endl;
		}
		stream << "      :: else -> skip;" << std::endl;

		stream << "      fi" << std::endl;
		stream << "      } /* d_step */" << std::endl;

	}

	TRACE_EXECUTION("Deqeued an external event");

	stream << "    }" << std::endl;
	//  stream << "  :: else -> quit;" << std::endl;
	stream << "    fi;" << std::endl;
	stream << "  }" << std::endl;
	stream << "  :: else -> skip;" << std::endl;
	stream << "  fi" << std::endl;
	stream << std::endl;
}
#endif

void ChartToPromela::writeFSMSelectTransitions(std::ostream& stream) {
	stream << "/* ---------------------------- */" << std::endl;
	stream << _prefix << "SELECT_TRANSITIONS:" << std::endl;

	stream << _prefix << "STATES_CLEAR(" << _prefix << "ctx.target_set)" << std::endl;
	stream << _prefix << "STATES_CLEAR(" << _prefix << "ctx.exit_set)" << std::endl;

	if (_transitions.size() > 0) {
		stream << _prefix << "TRANS_CLEAR(" << _prefix << "ctx.conflicts)" << std::endl;
		stream << _prefix << "TRANS_CLEAR(" << _prefix << "ctx.trans_set)" << std::endl;

		stream << "#if TRACE_EXECUTION" << std::endl;
		if (_machinesAll->size() > 1) {
			stream << "printf(\"%d: Establishing optimal transition set for event %d\\n\", _pid, " << _prefix << EVENT_NAME << " );" << std::endl;
		} else {
			stream << "printf(\"Establishing optimal transition set for event %d\\n\", " << _prefix << EVENT_NAME << " );" << std::endl;
		}
		stream << "#endif" << std::endl;
		stream << std::endl;

		stream << "#if TRACE_EXECUTION" << std::endl;
		stream << "printf(\"Configuration: \");" << std::endl;
		printBitArray(stream, _prefix + "config", _states.size());
		stream << "printf(\"\\n\");" << std::endl;
		stream << "#endif" << std::endl;
		stream << std::endl;
		stream << "  " << _prefix << "flags[USCXML_CTX_TRANSITION_FOUND] = false;" << std::endl;
		stream << "  i = 0;" << std::endl;
		stream << "  do" << std::endl;
		stream << "  :: i < " << _prefix << "USCXML_NUMBER_TRANS -> {" << std::endl;

		stream << "    /* only select non-history, non-initial transitions */" << std::endl;
		stream << "    if" << std::endl;
		stream << "    :: !" << _prefix << "transitions[i].type[USCXML_TRANS_HISTORY] &&" << std::endl;
		stream << "       !" << _prefix << "transitions[i].type[USCXML_TRANS_INITIAL] -> {" << std::endl;

		stream << "      if" << std::endl;
		stream << "      :: /* is the transition active? */" << std::endl;
		stream << "         " << _prefix << "config[" << _prefix << "transitions[i].source] && " << std::endl;
		stream << std::endl;
		stream << "         /* is it non-conflicting? */" << std::endl;
		stream << "         !" << _prefix << "ctx.conflicts[i] && " << std::endl;
		stream << std::endl;
		stream << "         /* is it spontaneous with an event or vice versa? */" << std::endl;
		stream << "         ((" << _prefix << EVENT_NAME << " == USCXML_EVENT_SPONTANEOUS && " << std::endl;
		stream << "           " << _prefix << "transitions[i].type[USCXML_TRANS_SPONTANEOUS]) || " << std::endl;
		stream << "          (" << _prefix << EVENT_NAME << " != USCXML_EVENT_SPONTANEOUS && " << std::endl;
		stream << "           !" << _prefix << "transitions[i].type[USCXML_TRANS_SPONTANEOUS])) &&" << std::endl;
		stream << std::endl;
		stream << "         /* is it matching and enabled? */" << std::endl;
		stream << "         (false " << std::endl;


		for (auto i = 0; i < _transitions.size(); i++) {
			stream << "          || (i == " << toStr(i);
			if (HAS_ATTR(_transitions[i], "event") && ATTR(_transitions[i], "event") != "*") {
				stream << " && (false";
				std::list<std::string> eventLiterals = tokenize(ATTR(_transitions[i], "event"));
				for (auto eventLiteral : eventLiterals) {
					if (boost::ends_with(eventLiteral, ".*")) {
						eventLiteral = eventLiteral.substr(0, eventLiteral.size() - 2);
					}
					if (boost::ends_with(eventLiteral, ".")) {
						eventLiteral = eventLiteral.substr(0, eventLiteral.size() - 1);
					}
					std::list<TrieNode*> events =_analyzer->getTrie().getWordsWithPrefix(eventLiteral);
					for (auto event : events) {
						stream << " || " << _prefix << EVENT_NAME << " == " << _analyzer->macroForLiteral(event->value);
					}
				}
				stream << ")";
			}
			if (HAS_ATTR(_transitions[i], "cond")) {
				stream << " && " << ADAPT_SRC(ATTR(_transitions[i], "cond"));
			}
			stream << ")" << std::endl;
		}

		stream << "         ) -> {" << std::endl;

		stream << "        /* remember that we found a transition */" << std::endl;
		stream << "        " << _prefix << "flags[USCXML_CTX_TRANSITION_FOUND] = true;" << std::endl;
		stream << std::endl;

		stream << "        /* transitions that are pre-empted */" << std::endl;
		stream << "        " << _prefix << "TRANS_OR(" << _prefix << "ctx.conflicts, " << _prefix << "transitions[i].conflicts)" << std::endl;
		stream << std::endl;

		stream << "        /* states that are directly targeted (resolve as entry-set later) */" << std::endl;
		stream << "        " << _prefix << "STATES_OR(" << _prefix << "ctx.target_set, " << _prefix << "transitions[i].target)" << std::endl;
		stream << std::endl;

		stream << "        /* states that will be left */" << std::endl;
		stream << "        " << _prefix << "STATES_OR(" << _prefix << "ctx.exit_set, " << _prefix << "transitions[i].exit_set)" << std::endl;
		stream << std::endl;

		stream << "        " << _prefix << "ctx.trans_set[i] = true;" << std::endl;


		stream << "      }" << std::endl;
		stream << "      :: else {" << std::endl;
		stream << "        skip;" << std::endl;
		stream << "      }" << std::endl;
		stream << "      fi" << std::endl;
		stream << "    }" << std::endl;
		stream << "    :: else -> {" << std::endl;
		stream << "      skip;" << std::endl;
		stream << "    }" << std::endl;
		stream << "    fi" << std::endl;

		stream << "    i = i + 1;" << std::endl;
		stream << "  }" << std::endl;
		stream << "  :: else -> break;" << std::endl;
		stream << "  od;" << std::endl;

		stream << "  " << _prefix << "STATES_AND(" << _prefix << "ctx.exit_set, " << _prefix << "config)" << std::endl;

		stream << std::endl;
		stream << "#if TRACE_EXECUTION" << std::endl;
		stream << "printf(\"Selected Transitions: \");" << std::endl;
		printBitArray(stream, _prefix + "ctx.trans_set", _transitions.size());
		stream << "printf(\"\\n\");" << std::endl;
		stream << "#endif" << std::endl;
		stream << std::endl;
	}
	stream << std::endl;
	stream << "#if TRACE_EXECUTION" << std::endl;
	stream << "printf(\"Target Set: \");" << std::endl;
	printBitArray(stream, _prefix + "ctx.target_set", _states.size());
	stream << "printf(\"\\n\");" << std::endl;
	stream << "#endif" << std::endl;
	stream << std::endl;

	stream << std::endl;
	stream << "#if TRACE_EXECUTION" << std::endl;
	stream << "printf(\"Exit Set: \");" << std::endl;
	printBitArray(stream, _prefix + "ctx.exit_set", _states.size());
	stream << "printf(\"\\n\");" << std::endl;
	stream << "#endif" << std::endl;
	stream << std::endl;

	stream << "  if" << std::endl;
	stream << "  :: !" << _prefix << "STATES_HAS_ANY(" << _prefix << "config) -> {" << std::endl;
	stream << "    /* Enter initial configuration */" << std::endl;
	stream << "    " << _prefix << "STATES_COPY(" << _prefix << "ctx.target_set, " << _prefix << "states[0].completion)" << std::endl;
	stream << "    " << _prefix << "flags[USCXML_CTX_SPONTANEOUS] = true;" << std::endl;
	stream << "    " << _prefix << "flags[USCXML_CTX_TRANSITION_FOUND] = true;" << std::endl;

	TRACE_EXECUTION("Entering initial default completion");

	//    stream << "    goto " << _prefix << "ESTABLISH_ENTRY_SET;" << std::endl;
	stream << std::endl;

	stream << "  }" << std::endl;
	stream << "  :: " << _prefix << "flags[USCXML_CTX_TRANSITION_FOUND] -> {" << std::endl;

	TRACE_EXECUTION("Found transitions");

	stream << "    " << _prefix << "flags[USCXML_CTX_SPONTANEOUS] = true;" << std::endl;
	stream << "  }" << std::endl;
	stream << "  :: else {" << std::endl;
	stream << "    " << _prefix << "flags[USCXML_CTX_SPONTANEOUS] = false;" << std::endl;

	TRACE_EXECUTION("Found NO transitions");

	//    stream << "    goto " << _prefix << "MICROSTEP;" << std::endl;
	stream << "  }" << std::endl;
	stream << "  fi" << std::endl;
	stream << std::endl;

}

void ChartToPromela::writeFSMRememberHistory(std::ostream& stream) {
	stream << "/* ---------------------------- */" << std::endl;
	stream << "/* REMEMBER_HISTORY: */" << std::endl;
	TRACE_EXECUTION("Save history configurations");

	stream << "  if" << std::endl;
	stream << "  :: " << _prefix << "STATES_HAS_ANY(" << _prefix << "config) -> {" << std::endl;
	stream << "    /* only remember history on non-initial entry */" << std::endl;

	stream << "    i = 0;" << std::endl;
	stream << "    do" << std::endl;
	stream << "    :: i < " << _prefix << "USCXML_NUMBER_STATES -> {" << std::endl;

	stream << "      if" << std::endl;
	stream << "      :: " << _prefix << "states[i].type[USCXML_STATE_HISTORY_SHALLOW] ||" << std::endl;
	stream << "         " << _prefix << "states[i].type[USCXML_STATE_HISTORY_DEEP] -> {" << std::endl;
	stream << "        if" << std::endl;
	stream << "        :: " << _prefix << "ctx.exit_set[" << _prefix << "states[i].parent] -> {" << std::endl;

	stream << "          /* a history state whose parent is about to be exited */" << std::endl;
	TRACE_EXECUTION_V("history state %d is about to be exited", "i");

	stream << std::endl;
	stream << "#if TRACE_EXECUTION" << std::endl;
	stream << "printf(\"COMPLET: \");" << std::endl;
	printBitArray(stream, _prefix + "states[i].completion", _states.size());
	stream << "printf(\"\\n\");" << std::endl;
	stream << "#endif" << std::endl;
	stream << std::endl;

	stream << "          " << _prefix << "STATES_COPY(" << _prefix << "ctx.tmp_states, " << _prefix << "states[i].completion)" << std::endl;

	stream << std::endl;
	stream << "          /* set those states who were enabled */" << std::endl;
	stream << "          " << _prefix << "STATES_AND(" << _prefix << "ctx.tmp_states, " << _prefix << "config)" << std::endl;

	stream << std::endl;
	stream << "#if TRACE_EXECUTION" << std::endl;
	stream << "printf(\"CONFIG : \");" << std::endl;
	printBitArray(stream, _prefix + "config", _states.size());
	stream << "printf(\"\\n\");" << std::endl;
	stream << "#endif" << std::endl;
	stream << std::endl;

	stream << std::endl;
	stream << "#if TRACE_EXECUTION" << std::endl;
	stream << "printf(\"TMP_STS: \");" << std::endl;
	printBitArray(stream, _prefix + "ctx.tmp_states", _states.size());
	stream << "printf(\"\\n\");" << std::endl;
	stream << "#endif" << std::endl;
	stream << std::endl;

	stream << std::endl;
	stream << "          /* clear current history with completion mask */" << std::endl;
	stream << "          " << _prefix << "STATES_AND_NOT(" << _prefix << "history, " << _prefix << "states[i].completion)" << std::endl;
	stream << std::endl;

	stream << "          /* set history */" << std::endl;
	stream << "          " << _prefix << "STATES_OR(" << _prefix << "history, " << _prefix << "ctx.tmp_states)" << std::endl;

	stream << std::endl;

	stream << "        }" << std::endl;
	stream << "        :: else -> skip;" << std::endl;
	stream << "        fi;" << std::endl;
	stream << "      }" << std::endl;
	stream << "      :: else -> skip;" << std::endl;
	stream << "      fi;" << std::endl;

	stream << "      i = i + 1;" << std::endl;
	stream << "    }" << std::endl;
	stream << "    :: else -> break;" << std::endl;
	stream << "    od;" << std::endl;
	stream << std::endl;

	stream << std::endl;
	stream << "#if TRACE_EXECUTION" << std::endl;
	stream << "printf(\"History: \");" << std::endl;
	printBitArray(stream, _prefix + "history", _states.size());
	stream << "printf(\"\\n\");" << std::endl;
	stream << "#endif" << std::endl;
	stream << "  }" << std::endl;
	stream << "  :: else -> skip;" << std::endl;
	stream << "  fi;" << std::endl;
}

void ChartToPromela::writeFSMEstablishEntrySet(std::ostream& stream) {
	stream << "/* ---------------------------- */" << std::endl;
	stream << _prefix << "ESTABLISH_ENTRY_SET:" << std::endl;
	stream << "  /* calculate new entry set */" << std::endl;
	stream << "  " << _prefix << "STATES_COPY(" << _prefix << "ctx.entry_set, " << _prefix << "ctx.target_set)" << std::endl;
	stream << std::endl;

	stream << "  i = 0;" << std::endl;
	stream << "  do" << std::endl;
	stream << "  :: i < " << _prefix << "USCXML_NUMBER_STATES -> {" << std::endl;

	stream << "    if" << std::endl;
	stream << "    :: " << _prefix << "ctx.entry_set[i] -> {" << std::endl;
	stream << "      /* ancestor completion */" << std::endl;
	stream << "      " << _prefix << "STATES_OR(" << _prefix << "ctx.entry_set, " << _prefix << "states[i].ancestors)" << std::endl;

	stream << "    }" << std::endl;
	stream << "    :: else -> skip;" << std::endl;
	stream << "    fi;" << std::endl;

	stream << "    i = i + 1;" << std::endl;
	stream << "  }" << std::endl;
	stream << "  :: else -> break;" << std::endl;
	stream << "  od;" << std::endl;
	stream << std::endl;

	stream << "  /* iterate for descendants */" << std::endl;
	stream << "  i = 0;" << std::endl;
	stream << "  do" << std::endl;
	stream << "  :: i < " << _prefix << "USCXML_NUMBER_STATES -> {" << std::endl;
	stream << "    if" << std::endl;
	stream << "    :: " << _prefix << "ctx.entry_set[i] -> {" << std::endl;
	stream << "      if" << std::endl;

	stream << "      :: " << _prefix << "states[i].type[USCXML_STATE_PARALLEL] -> {" << std::endl;
	stream << "        " << _prefix << "STATES_OR(" << _prefix << "ctx.entry_set, " << _prefix << "states[i].completion)" << std::endl;
	stream << "      }" << std::endl;


	stream << "      :: " << _prefix << "states[i].type[USCXML_STATE_HISTORY_SHALLOW] ||" << std::endl;
	stream << "         " << _prefix << "states[i].type[USCXML_STATE_HISTORY_DEEP] -> {" << std::endl;

	TRACE_EXECUTION_V("Descendant completion for history state %d", "i")

	stream << "        if" << std::endl;
	stream << "        :: !" << _prefix << "STATES_HAS_AND(" << _prefix << "states[i].completion, " << _prefix << "history)";
	//	bit_has_and(stream, _prefix + "states[i].completion", _prefix + "history", _states.size(), 5);
	stream << " && !" << _prefix << "config[" << _prefix << "states[i].parent]" << " -> {" << std::endl;
	stream << "          /* nothing set for history, look for a default transition */" << std::endl;
	TRACE_EXECUTION("Fresh history in target set")
	if (_transitions.size() > 0) {
		stream << "          j = 0;" << std::endl;
		stream << "          do" << std::endl;
		stream << "          :: j < " << _prefix << "USCXML_NUMBER_TRANS -> {" << std::endl;
		stream << "             if" << std::endl;
		stream << "             :: " << _prefix << "transitions[j].source == i -> {" << std::endl;
		stream << "               " << _prefix << "ctx.trans_set[j] = true;" << std::endl;

		stream << "               " << _prefix << "STATES_OR(" << _prefix << "ctx.entry_set, " << _prefix << "transitions[j].target)" << std::endl;
		stream << std::endl;
		stream << "               if" << std::endl;
		stream << "               :: (" << _prefix << "states[i].type[USCXML_STATE_HISTORY_DEEP] &&" << std::endl;
		stream << "                   !" << _prefix << "STATES_HAS_AND(" << _prefix << "transitions[j].target, " << _prefix << "states[i].children)";
		//    bit_has_and(stream, _prefix + "transitions[j].target", _prefix + "states[i].children", _states.size(), 10);
		stream << "                  ) -> {" << std::endl;
		stream << "                 k = i + 1" << std::endl;
		stream << "                 do" << std::endl;
		stream << "                 :: k < " << _prefix << "USCXML_NUMBER_STATES -> {" << std::endl;
		stream << "                   if" << std::endl;
		stream << "                   :: " << _prefix << "transitions[j].target[k] -> {" << std::endl;
		stream << "                     " << _prefix << "STATES_OR(" << _prefix << "ctx.entry_set, " << _prefix << "states[k].ancestors)" << std::endl;
		stream << "                     break;" << std::endl;
		stream << std::endl;
		stream << "                   }" << std::endl;
		stream << "                   :: else -> skip;" << std::endl;
		stream << "                   fi" << std::endl;
		stream << "                   k = k + 1;" << std::endl;
		stream << "                 }" << std::endl;
		stream << "                 :: else -> break;" << std::endl;
		stream << "                 od" << std::endl;
		stream << "               }" << std::endl;
		stream << "               :: else -> skip;" << std::endl;
		stream << "               fi" << std::endl;
		stream << "               break;" << std::endl;
		stream << "             }" << std::endl;
		stream << "             :: else -> skip;" << std::endl;
		stream << "             fi" << std::endl;
		stream << "             j = j + 1;" << std::endl;
		stream << "          }" << std::endl;
		stream << "          :: else -> break" << std::endl;
		stream << "          od" << std::endl;
	}
	stream << "          skip;" << std::endl;
	stream << "        }" << std::endl;
	stream << "        :: else -> {" << std::endl;

	TRACE_EXECUTION("Established history in target set")
	stream << "          " << _prefix << "STATES_COPY(" << _prefix << "ctx.tmp_states, " << _prefix << "states[i].completion)" << std::endl;
	stream << "          " << _prefix << "STATES_AND(" << _prefix << "ctx.tmp_states, " << _prefix << "history)" << std::endl;
	stream << "          " << _prefix << "STATES_OR(" << _prefix << "ctx.entry_set, " << _prefix << "ctx.tmp_states)" << std::endl;
	stream << "          if" << std::endl;
	stream << "          :: " << _prefix << "states[i].type[USCXML_STATE_HAS_HISTORY] ||" << std::endl;
	stream << "             " << _prefix << "states[i].type[USCXML_STATE_HISTORY_DEEP] -> { " << std::endl;
	stream << "            /* a deep history state with nested histories -> more completion */" << std::endl;
	TRACE_EXECUTION("DEEP HISTORY")
	stream << "            j = i + 1;" << std::endl;
	stream << "            do" << std::endl;
	stream << "            :: j < " << _prefix << "USCXML_NUMBER_STATES -> {" << std::endl;
	stream << "              if" << std::endl;
	stream << "              :: (" << _prefix << "states[i].completion[j] &&" << std::endl;
	stream << "                  " << _prefix << "ctx.entry_set[j] && " << std::endl;
	stream << "                  " << _prefix << "states[j].type[USCXML_STATE_HAS_HISTORY]) -> {" << std::endl;
	stream << "                k = j + 1;" << std::endl;
	stream << "                do" << std::endl;
	stream << "                :: k < " << _prefix << "USCXML_NUMBER_STATES -> {" << std::endl;
	stream << "                  /* add nested history to entry_set */" << std::endl;
	stream << "                  if" << std::endl;
	stream << "                  :: (" << _prefix << "states[k].type[USCXML_STATE_HISTORY_DEEP] ||" << std::endl;
	stream << "                      " << _prefix << "states[k].type[USCXML_STATE_HISTORY_SHALLOW]) &&" << std::endl;
	stream << "                     " << _prefix << "states[j].children[k] -> {" << std::endl;
	stream << "                    /* a nested history state */" << std::endl;
	stream << "                    " << _prefix << "ctx.entry_set[k] = true;" << std::endl;
	stream << "                  }" << std::endl;
	stream << "                  :: else -> skip;" << std::endl;
	stream << "                  fi" << std::endl;
	stream << "                  k = k + 1;" << std::endl;
	stream << "                }" << std::endl;
	stream << "                :: else -> break;" << std::endl;
	stream << "                od" << std::endl;
	stream << "              }" << std::endl;
	stream << "              :: else -> skip;" << std::endl;
	stream << "              fi" << std::endl;
	stream << "            }" << std::endl;
	stream << "            j = j + 1;" << std::endl;
	stream << "            :: else -> break;" << std::endl;
	stream << "            od" << std::endl;
	stream << "          }" << std::endl;
	stream << "          :: else -> skip;" << std::endl;
	stream << "          fi" << std::endl;

	stream << "        }" << std::endl;
	stream << "        fi;" << std::endl;

	stream << "      }" << std::endl;

	if (_transitions.size() > 0) {
		stream << "      :: " << _prefix << "states[i].type[USCXML_STATE_INITIAL] -> {" << std::endl;

		TRACE_EXECUTION_V("Descendant completion for initial state %d", "i")

		stream << "        j = 0" << std::endl;
		stream << "        do" << std::endl;
		stream << "        :: j < " << _prefix << "USCXML_NUMBER_TRANS -> {" << std::endl;
		stream << "          if" << std::endl;
		stream << "          :: " << _prefix << "transitions[j].source == i -> {" << std::endl;
		stream << "            " << _prefix << "ctx.trans_set[j] = true;" << std::endl;
		stream << "            " << _prefix << "ctx.entry_set[i] = false;" << std::endl;

		TRACE_EXECUTION_V("Adding transition %d!", "j");


		stream << "            " << _prefix << "STATES_OR(" << _prefix << "ctx.entry_set, " << _prefix << "transitions[j].target)" << std::endl;
		stream << std::endl;

		stream << "            k = i + 1;" << std::endl;
		stream << "            do" << std::endl;
		stream << "            :: k < " << _prefix << "USCXML_NUMBER_STATES -> {" << std::endl;
		stream << "              if" << std::endl;
		stream << "              :: " << _prefix << "transitions[j].target[k] -> {" << std::endl;

		stream << "                " << _prefix << "STATES_OR(" << _prefix << "ctx.entry_set, " << _prefix << "states[k].ancestors)" << std::endl;
		stream << std::endl;

		stream << "              }" << std::endl;
		stream << "              :: else -> break;" << std::endl;
		stream << "              fi" << std::endl;
		stream << "              k = k + 1;" << std::endl;
		stream << "            }" << std::endl;
		stream << "            :: else -> break" << std::endl;
		stream << "            od" << std::endl;
		stream << "          }" << std::endl;
		stream << "          :: else -> skip;" << std::endl;
		stream << "          fi" << std::endl;
		stream << "          j = j + 1;" << std::endl;
		stream << "        }" << std::endl;
		stream << "        :: else -> break" << std::endl;
		stream << "        od;" << std::endl;

		stream << "      }" << std::endl;
	}

	stream << "      :: " << _prefix << "states[i].type[USCXML_STATE_COMPOUND] -> {" << std::endl;

	//    TRACE_EXECUTION_V("Descendant completion for compound state %d", "i")

	stream << "        /* we need to check whether one child is already in entry_set */" << std::endl;
	stream << "        if" << std::endl;
	stream << "        :: (" << std::endl;
	stream << "          !" << _prefix << "STATES_HAS_AND(" << _prefix << "ctx.entry_set, " << _prefix << "states[i].children)";
	stream << " && " << std::endl;
	stream << "           (!" << _prefix << "STATES_HAS_AND(" << _prefix << "config, " << _prefix << "states[i].children)";
	//	bit_has_and(stream, _prefix + "config", _prefix + "states[i].children", _states.size(), 5);
	stream << " || " << _prefix << "STATES_HAS_AND(" << _prefix << "ctx.exit_set, " << _prefix << "states[i].children)" << std::endl;
	stream << ")) " << std::endl;
	stream << "        -> {" << std::endl;

	stream << "          " << _prefix << "STATES_OR(" << _prefix << "ctx.entry_set, " << _prefix << "states[i].completion)" << std::endl;

	stream << "          if" << std::endl;
	stream << "          :: (" << _prefix << "STATES_HAS_AND(" << _prefix << "states[i].completion, " << _prefix << "states[i].children)";
	//	bit_has_and(stream, _prefix + "states[i].completion", _prefix + "states[i].children", _states.size(), 6);
	stream << std::endl;
	stream << "          ) -> {" << std::endl;
	stream << "            /* deep completion */" << std::endl;
	stream << "            j = i + 1;" << std::endl;

	//    TRACE_EXECUTION_V("Deep completion for compound state %d", "i")

	stream << "            do" << std::endl;
	stream << "            :: j < " << _prefix << "USCXML_NUMBER_STATES - 1 -> {" << std::endl;
	stream << "              j = j + 1;" << std::endl;
	stream << "              if" << std::endl;
	stream << "              :: " << _prefix << "states[i].completion[j] -> {" << std::endl;

	stream << "                " << _prefix << "STATES_OR(" << _prefix << "ctx.entry_set, " << _prefix << "states[j].ancestors)" << std::endl;
	stream << std::endl;

	stream << "                /* completion of compound is single state */" << std::endl;
	stream << "                break;" << std::endl;
	stream << "              } " << std::endl;
	stream << "              :: else -> skip;" << std::endl;
	stream << "              fi" << std::endl;
	stream << "            }" << std::endl;
	stream << "            :: else -> break;" << std::endl;
	stream << "            od" << std::endl;

	stream << "          }" << std::endl;
	stream << "          :: else -> skip;" << std::endl;
	stream << "          fi" << std::endl;

	stream << "        }" << std::endl;
	stream << "        :: else -> skip;" << std::endl;
	stream << "        fi" << std::endl;
	stream << "      }" << std::endl;

	stream << "      :: else -> skip;" << std::endl;
	stream << "      fi;" << std::endl;
	stream << "    }" << std::endl;
	stream << "    :: else -> skip;" << std::endl;
	stream << "    fi;" << std::endl;
	stream << "    i = i + 1;" << std::endl;
	stream << "  }" << std::endl;
	stream << "  :: else -> break;" << std::endl;
	stream << "  od;" << std::endl;
	stream << std::endl;

	stream << std::endl;
	stream << "#if TRACE_EXECUTION" << std::endl;
	stream << "printf(\"Entry Set\");" << std::endl;
	printBitArray(stream, _prefix + "ctx.entry_set", _states.size());
	stream << "printf(\"\\n\");" << std::endl;
	stream << "#endif" << std::endl;
	stream << std::endl;
}

void ChartToPromela::writeFSMExitStates(std::ostream& stream) {
	stream << "/* ---------------------------- */" << std::endl;
	stream << "/* EXIT_STATES: */" << std::endl;
	stream << "  i = " << _prefix << "USCXML_NUMBER_STATES;" << std::endl;
	stream << "  do" << std::endl;
	stream << "  :: i > 0 -> {" << std::endl;
	stream << "    i = i - 1;" << std::endl;
	stream << "    if" << std::endl;
	stream << "    :: " << _prefix << "ctx.exit_set[i] && " << _prefix << "config[i] -> {" << std::endl;
	stream << "      /* call all on-exit handlers */" << std::endl;

	TRACE_EXECUTION_V("Exiting state %d", "i");

	stream << "      if" << std::endl;
	for (auto i = 0; i < _states.size(); i++) {
		std::list<DOMElement*> onexits = DOMUtils::filterChildElements(XML_PREFIX(_states[i]).str() + "onexit" , _states[i]);
		if (onexits.size() > 0) {
			stream << "      :: i == " << toStr(i) << " -> {" << std::endl;
			TRACE_EXECUTION_V("Processing executable content for exiting state %d", "i");
			for (auto onexit : onexits)
				writeExecContent(stream, onexit, 3);
			stream << "      }" << std::endl;
		}
	}
	stream << "      :: else -> skip;" << std::endl;
	stream << "      fi" << std::endl;
	stream << std::endl;

	stream << "      " << _prefix << "config[i] = false;" << std::endl;
	stream << "      skip;" << std::endl;
	stream << "    }" << std::endl;
	stream << "    :: else -> skip;" << std::endl;
	stream << "    fi;" << std::endl;
	stream << "  }" << std::endl;
	stream << "  :: else -> break;" << std::endl;
	stream << "  od;" << std::endl;
	stream << std::endl;
}

void ChartToPromela::writeFSMTakeTransitions(std::ostream& stream) {
	stream << "/* ---------------------------- */" << std::endl;
	stream << "/* TAKE_TRANSITIONS: */" << std::endl;
	if (_transitions.size() > 0) {
		stream << "  i = 0;" << std::endl;
		stream << "  do" << std::endl;
		stream << "  :: i < " << _prefix << "USCXML_NUMBER_TRANS -> {" << std::endl;
		stream << "    if" << std::endl;
		stream << "    :: " << _prefix << "ctx.trans_set[i] && " << std::endl;
		stream << "       !" << _prefix << "transitions[i].type[USCXML_TRANS_HISTORY] && " << std::endl;
		stream << "       !" << _prefix << "transitions[i].type[USCXML_TRANS_INITIAL] -> {" << std::endl;
		stream << "      /* Call executable content in normal transition */" << std::endl;

		TRACE_EXECUTION_V("Taking transition %d", "i");

		stream << "      if" << std::endl;
		for (auto i = 0; i < _transitions.size(); i++) {
			stream << "      :: i == " << toStr(i) << " -> {" << std::endl;
			TRACE_EXECUTION_V("Processing executable content for transition %d", "i");
			writeExecContent(stream, _transitions[i], 4);
			stream << "        skip;" << std::endl;
			stream << "      }" << std::endl;
		}
		stream << "      :: else ->skip;" << std::endl;
		stream << "      fi" << std::endl;
		stream << std::endl;
		stream << "    }" << std::endl;
		stream << "    :: else -> skip;" << std::endl;
		stream << "    fi;" << std::endl;
		stream << "    i = i + 1;" << std::endl;
		stream << "  }" << std::endl;
		stream << "  :: else -> break;" << std::endl;
		stream << "  od;" << std::endl;
	}
}

void ChartToPromela::writeFSMEnterStates(std::ostream& stream) {
	stream << "/* ---------------------------- */" << std::endl;
	stream << "/* ENTER_STATES: */" << std::endl;
	stream << "  i = 0;" << std::endl;
	stream << "  do" << std::endl;
	stream << "  :: i < " << _prefix << "USCXML_NUMBER_STATES -> {" << std::endl;
	stream << "    if" << std::endl;
	stream << "    :: (" << _prefix << "ctx.entry_set[i] &&" << std::endl;
	stream << "        !" << _prefix << "config[i] && " << std::endl;
	stream << "        /* these are no proper states */" << std::endl;
	stream << "        !" << _prefix << "states[i].type[USCXML_STATE_HISTORY_DEEP] && " << std::endl;
	stream << "        !" << _prefix << "states[i].type[USCXML_STATE_HISTORY_SHALLOW] && " << std::endl;
	stream << "        !" << _prefix << "states[i].type[USCXML_STATE_INITIAL]" << std::endl;
	stream << "       ) -> {" << std::endl;

	TRACE_EXECUTION_V("Entering state %d", "i");

	stream << "         " << _prefix << "config[i] = true;" << std::endl;
	stream << std::endl;

#if 0
	stream << "         if" << std::endl;
	stream << "         :: !" << _prefix << "initialized_data[i] -> {" << std::endl;
	stream << "           /* TODO: late data binding not supported yet */" << std::endl;
	stream << "           " << _prefix << "initialized_data[i] = true;" << std::endl;
	stream << "           skip" << std::endl;
	stream << "         }" << std::endl;
	stream << "         :: else -> skip;" << std::endl;
	stream << "         fi" << std::endl;
	stream << std::endl;
#endif

	stream << "         /* Process executable content for entering a state */" << std::endl;
	stream << "         if" << std::endl;
	for (auto i = 0; i < _states.size(); i++) {
		std::list<DOMElement*> onentries = DOMUtils::filterChildElements(XML_PREFIX(_states[i]).str() + "onentry" , _states[i]);
		if (onentries.size() > 0) {
			stream << "         :: i == " << toStr(i) << " -> {" << std::endl;
			TRACE_EXECUTION_V("Processing executable content for entering state %d", "i");
			for (auto onentry : onentries)
				writeExecContent(stream, onentry, 5);
			stream << "         }" << std::endl;
		}
	}
	stream << "         :: else ->skip;" << std::endl;
	stream << "         fi" << std::endl;
	stream << std::endl;

	stream << "         /* take history and initial transitions */" << std::endl;
	if (_transitions.size() > 0) {
		stream << "         j = 0;" << std::endl;
		stream << "         do" << std::endl;
		stream << "         :: j < " << _prefix << "USCXML_NUMBER_TRANS -> {" << std::endl;
		stream << "           if" << std::endl;
		stream << "           :: (" << _prefix << "ctx.trans_set[j] &&" << std::endl;
		stream << "              (" << _prefix << "transitions[j].type[USCXML_TRANS_HISTORY] ||" << std::endl;
		stream << "               " << _prefix << "transitions[j].type[USCXML_TRANS_INITIAL]) && " << std::endl;
		stream << "               " << _prefix << "states[" << _prefix << "transitions[j].source].parent == i) -> {" << std::endl;
		stream << "              /* Call executable content in history or initial transition */" << std::endl;
		stream << "              if" << std::endl;
		for (auto i = 0; i < _transitions.size(); i++) {
			stream << "              :: j == " << toStr(i) << " -> {" << std::endl;
			TRACE_EXECUTION_V("Processing executable content for transition %d", "j");

			writeExecContent(stream, _transitions[i], 8);
			stream << "                skip;" << std::endl;
			stream << "              }" << std::endl;
		}
		stream << "              :: else ->skip;" << std::endl;
		stream << "              fi" << std::endl;
		stream << std::endl;

		stream << "           }" << std::endl;
		stream << "           :: else -> skip;" << std::endl;
		stream << "           fi" << std::endl;
		stream << "           j = j + 1;" << std::endl;
		stream << "         }" << std::endl;
		stream << "         :: else -> break;" << std::endl;
		stream << "         od" << std::endl;
	}

	stream << "         /* handle final states */" << std::endl;
	stream << "         if" << std::endl;
	stream << "         :: " << _prefix << "states[i].type[USCXML_STATE_FINAL] -> {" << std::endl;

	stream << "           if" << std::endl;
	stream << "           :: " << _prefix << "states[" << _prefix << "states[i].parent].children[1] -> {" << std::endl;
	stream << "             /* exit topmost SCXML state */" << std::endl;
	stream << "             " << _prefix << "flags[USCXML_CTX_TOP_LEVEL_FINAL] = true;" << std::endl;
	stream << "             " << _prefix << "flags[USCXML_CTX_FINISHED] = true;" << std::endl;
	stream << "           }" << std::endl;
	stream << "           :: else -> {" << std::endl;
	stream << "             /* raise done event */" << std::endl;
	stream << "             if" << std::endl;

	std::string insertOp = "!";
	//    if (_analyzer->usesEventField("delay"))
	//        insertOp += "!";

	for (auto state : _states) {
		if (state->getParentNode() == NULL || state->getParentNode()->getNodeType() != DOMNode::ELEMENT_NODE)
			continue;

		if (!isFinal(state))
			continue;

		DOMElement* parent = static_cast<DOMElement*>(state->getParentNode());
		if (!HAS_ATTR(parent, "id"))
			continue;

		std::string doneEvent = _analyzer->macroForLiteral("done.state." + ATTR_CAST(state->getParentNode(), "id"));

		stream << "             :: (i == " << ATTR(state, "documentOrder") << ") -> {" << std::endl;

		if (_analyzer->usesComplexEventStruct()) {
			std::string typeReset = _analyzer->getTypeReset(_prefix + "_tmpE", _analyzer->getType("_event"), 7);
			stream << typeReset << std::endl;
			stream << "               " << _prefix << "_tmpE.name = " << doneEvent << ";" << std::endl;

			std::list<DOMElement*> donedatas = DOMUtils::filterChildElements(XML_PREFIX(state).str() + "donedata" , state);
			if (donedatas.size() > 0) {
				writeRaiseDoneDate(stream, donedatas.front(), 8);
			}

			doneEvent = _prefix + "_tmpE";
		}


		stream << "               " << _prefix << "iQ" << insertOp << doneEvent << ";" << std::endl;
		stream << "             }" << std::endl;

	}
	stream << "             :: else -> skip;" << std::endl;
	stream << "             fi" << std::endl;

	stream << "           }" << std::endl;
	stream << "           fi" << std::endl;

	stream << "           /**" << std::endl;
	stream << "            * are we the last final state to leave a parallel state?:" << std::endl;
	stream << "            * 1. Gather all parallel states in our ancestor chain" << std::endl;
	stream << "            * 2. Find all states for which these parallels are ancestors" << std::endl;
	stream << "            * 3. Iterate all active final states and remove their ancestors" << std::endl;
	stream << "            * 4. If a state remains, not all children of a parallel are final" << std::endl;
	stream << "            */" << std::endl;
	stream << "            j = 0;" << std::endl;
	stream << "            do" << std::endl;
	stream << "            :: j < " << _prefix << "USCXML_NUMBER_STATES -> {" << std::endl;
	stream << "              if" << std::endl;
	stream << "              :: " << _prefix << "states[j].type[USCXML_STATE_PARALLEL] && " << _prefix << "states[i].ancestors[j] -> {" << std::endl;
	stream << "                " << _prefix << "STATES_CLEAR(" << _prefix << "ctx.tmp_states)" << std::endl;

	stream << "                k = 0;" << std::endl;
	stream << "                do" << std::endl;
	stream << "                :: k < " << _prefix << "USCXML_NUMBER_STATES -> {" << std::endl;
	stream << "                  if" << std::endl;
	stream << "                  :: " << _prefix << "states[k].ancestors[j] && " << _prefix << "config[k] -> {" << std::endl;
	stream << "                    if" << std::endl;
	stream << "                    :: " << _prefix << "states[k].type[USCXML_STATE_FINAL] -> {" << std::endl;

	stream << "                      " << _prefix << "STATES_AND_NOT(" << _prefix << "ctx.tmp_states, " << _prefix << "states[k].ancestors)" << std::endl;
	stream << "                    }" << std::endl;
	stream << "                    :: else -> {" << std::endl;

	stream << "                      " << _prefix << "ctx.tmp_states[k] = true;" << std::endl;
	stream << "                    }" << std::endl;
	stream << "                    fi" << std::endl;
	stream << "                  }" << std::endl;
	stream << "                  :: else -> skip;" << std::endl;
	stream << "                  fi" << std::endl;
	stream << "                  k = k + 1;" << std::endl;
	stream << "                }" << std::endl;
	stream << "                :: else -> break;" << std::endl;
	stream << "                od" << std::endl;
	stream << "                if" << std::endl;
	stream << "                :: !" << _prefix << "STATES_HAS_ANY(" << _prefix << "ctx.tmp_states) -> {" << std::endl;
	stream << "                  if" << std::endl;

	for (auto state : _states) {
		if (isParallel(state) && HAS_ATTR(state, "id")) {
			stream << "                  :: j == " << toStr(ATTR(state, "documentOrder")) << " -> {" << std::endl;

			std::string doneEvent = _analyzer->macroForLiteral("done.state." + ATTR(state, "id"));

			if (_analyzer->usesComplexEventStruct()) {
				std::string typeReset = _analyzer->getTypeReset(_prefix + "_tmpE", _analyzer->getType("_event"), 10);
				stream << typeReset << std::endl;
				stream << "                    " << _prefix << "_tmpE.name = " << doneEvent << ";" << std::endl;

				std::list<DOMElement*> donedatas = DOMUtils::filterChildElements(XML_PREFIX(state).str() + "donedata" , state);
				if (donedatas.size() > 0) {
					writeRaiseDoneDate(stream, donedatas.front(), 11);
				}
				doneEvent = _prefix + "_tmpE";
			}

			stream << "                    " << _prefix << "iQ" << insertOp << doneEvent << ";" << std::endl;
			stream << "                  }" << std::endl;
		}
	}

	stream << "                  :: else -> skip;" << std::endl;
	stream << "                  fi" << std::endl;

	stream << "                }" << std::endl;
	stream << "                :: else -> skip;" << std::endl;
	stream << "                fi" << std::endl;
	stream << "              }" << std::endl;
	stream << "              :: else -> skip;" << std::endl;
	stream << "              fi" << std::endl;
	stream << "              j = j + 1;" << std::endl;
	stream << "            }" << std::endl;
	stream << "            :: else -> break;" << std::endl;
	stream << "            od" << std::endl;


	stream << "         }" << std::endl;
	stream << "         :: else -> skip;" << std::endl;
	stream << "         fi" << std::endl;

	stream << std::endl;

	stream << "    }" << std::endl;
	stream << "    :: else -> skip;" << std::endl;
	stream << "    i = i + 1;" << std::endl;
	stream << "    fi;" << std::endl;
	stream << "  }" << std::endl;
	stream << "  :: else -> break;" << std::endl;
	stream << "  od;" << std::endl;
}

void ChartToPromela::writeFSMTerminateMachine(std::ostream& stream) {
	stream << "/* ---------------------------- */" << std::endl;
	stream << _prefix << "TERMINATE_MACHINE:" << std::endl;

	stream << "skip; d_step {" << std::endl;

	TRACE_EXECUTION("Machine finished");

	stream << "/* exit all remaining states */" << std::endl;
	stream << "i = " << _prefix << "USCXML_NUMBER_STATES;" << std::endl;
	stream << "do" << std::endl;
	stream << ":: i > 0 -> {" << std::endl;
	stream << "  i = i - 1;" << std::endl;
	stream << "  if" << std::endl;
	stream << "  :: " << _prefix << "config[i] && " << _prefix << "flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {" << std::endl;
	stream << "    /* call all on exit handlers */" << std::endl;
	stream << "   if" << std::endl;
	for (auto i = 0; i < _states.size(); i++) {
		std::list<DOMElement*> onentries = DOMUtils::filterChildElements(XML_PREFIX(_states[i]).str() + "onexit" , _states[i]);
		if (onentries.size() > 0) {
			stream << "    :: i == " << toStr(i) << " -> {" << std::endl;
			TRACE_EXECUTION_V("Processing executable content for exiting state %d", "i");
			for (auto onentry : onentries)
				writeExecContent(stream, onentry, 2);
			stream << "    }" << std::endl;
		}
	}
	stream << "    :: else -> skip;" << std::endl;
	stream << "    fi" << std::endl;
	stream << std::endl;
	stream << "    skip;" << std::endl;
	stream << "    " << std::endl;
	stream << "  }" << std::endl;
	stream << "  :: else -> skip;" << std::endl;
	stream << "  fi;" << std::endl;
	stream << std::endl;

	stream << "  if" << std::endl;
	stream << "  :: " << _prefix << "invocations[i] -> {" << std::endl;
	stream << "    /* cancel invocations */" << std::endl;
	stream << "    " << _prefix << "invocations[i] = false;" << std::endl;
	stream << "    if" << std::endl;

	for (auto machine : _machinesNested) {
		stream << "    :: i == " << ATTR_CAST(machine.first->getParentNode(), "documentOrder") << " -> {" << std::endl;
		stream << "      " << machine.second->_prefix << "flags[USCXML_CTX_FINISHED] = true;" << std::endl;
		stream << "    }" << std::endl;
	}
	stream << "    :: else -> skip;" << std::endl;
	stream << "    fi" << std::endl;

	stream << "    skip;" << std::endl;
	stream << std::endl;
	stream << "  }" << std::endl;
	stream << "  :: else -> skip;" << std::endl;
	stream << "  fi;" << std::endl;
	stream << "}" << std::endl;
	stream << ":: else -> break;" << std::endl;
	stream << "od;" << std::endl;

	stream << std::endl;

	if (_machinesAll->size() > 1 && _analyzer->usesEventField("delay")) {
		/* TODO: We nee to clear all events if we were canceled */
		TRACE_EXECUTION("Removing pending events");
		stream << "removePendingEventsFromInvoker(" << _analyzer->macroForLiteral(_invokerid) << ")" << std::endl;
	}


	if (_parent != NULL) {
		stream << "/* send done event */" << std::endl;
		stream << "if" << std::endl;
		stream << ":: " << _prefix << "flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {" << std::endl;

		if (_analyzer->usesComplexEventStruct()) {
			std::string typeReset = _analyzer->getTypeReset(_prefix + "_tmpE", _analyzer->getType("_event"), 2);
			stream << typeReset << std::endl;
			stream << "    " << _prefix << "_tmpE.name = " << _analyzer->macroForLiteral("done.invoke." + _invokerid) << std::endl;

			if (_analyzer->usesEventField("invokeid")) {
				stream << "    " << _prefix << "_tmpE.invokeid = " << _analyzer->macroForLiteral(_invokerid) << std::endl;
			}

		} else {
			stream << "    " << _prefix << "_tmpE = " << _analyzer->macroForLiteral("done.invoke." + _invokerid) << std::endl;
		}


		TRACE_EXECUTION("Sending DONE.INVOKE");

		stream << "    " << _parent->_prefix << "eQ!" << _prefix << "_tmpE;" << std::endl;
		if (_analyzer->usesEventField("delay")) {
			stream << "    insertWithDelay(" << _parent->_prefix << "eQ);" << std::endl;
		}
		stream << "}" << std::endl;
		stream << ":: else -> skip" << std::endl;
		stream << "fi;" << std::endl;
		stream << std::endl;

	}
	stream << "} /* d_step */" << std::endl;

}

void ChartToPromela::writeIfBlock(std::ostream& stream, std::list<DOMElement*>& condChain, size_t indent) {
	if (condChain.size() == 0)
		return;

	std::string padding;
	for (size_t i = 0; i < indent; i++) {
		padding += "  ";
	}

	bool noNext = condChain.size() == 1;
	bool nextIsElse = false;

	DOMElement* ifNode = condChain.front();
	condChain.pop_front();

	if (condChain.size() > 0) {
		if (TAGNAME_CAST(condChain.front()) == "else") {
			nextIsElse = true;
		}
	}

	stream << padding << "if" << std::endl;
	// we need to nest the elseifs to resolve promela if semantics
	stream << padding << ":: (" << ADAPT_SRC(ATTR(ifNode, "cond")) << ") -> {" << std::endl;

	DOMNode* child;
	if (TAGNAME(ifNode) == "if") {
		child = ifNode->getFirstChild();
	} else {
		child = ifNode->getNextSibling();
	}
	while(child) {
		if (child->getNodeType() == DOMNode::ELEMENT_NODE) {
			DOMElement* childElem = static_cast<DOMElement*>(child);
			if (TAGNAME(childElem) == "elseif" || TAGNAME_CAST(childElem) == "else")
				break;
			writeExecContent(stream, childElem, indent + 1);
		}
		child = child->getNextSibling();
	}
	stream << padding << "}" << std::endl;
	stream << padding << ":: else -> ";

	if (nextIsElse) {
		child = condChain.front()->getNextSibling();
		stream << "{" << std::endl;
		while(child) {
			if (child->getNodeType() == DOMNode::ELEMENT_NODE) {
				writeExecContent(stream, child, indent + 1);
			}
			child = child->getNextSibling();
		}
		stream << padding << "}" << std::endl;

	} else if (noNext) {
		stream << "skip;" << std::endl;
	} else {
		stream << "{" << std::endl;
		writeIfBlock(stream, condChain, indent + 1);
		stream << padding << "}" << std::endl;
	}

	stream << padding << "fi;" << std::endl;

}

std::string ChartToPromela::beautifyIndentation(const std::string& code, size_t indent) {

	std::string padding;
	for (size_t i = 0; i < indent; i++) {
		padding += "  ";
	}

	// remove topmost indentation from every line and reindent
	std::stringstream beautifiedSS;

	std::string initialIndent;
	bool gotIndent = false;
	bool isFirstLine = true;
	std::stringstream ssLine(code);
	std::string line;

	while(std::getline(ssLine, line)) {
		size_t firstChar = line.find_first_not_of(" \t\r\n");
		if (firstChar != std::string::npos) {
			if (!gotIndent) {
				initialIndent = line.substr(0, firstChar);
				gotIndent = true;
			}
			beautifiedSS << (isFirstLine ? "" : "\n") << padding << boost::replace_first_copy(line, initialIndent, "");
			isFirstLine = false;
		}
	}

	return beautifiedSS.str();
}

std::string ChartToPromela::dataToAssignments(const std::string& prefix, const Data& data) {
	std::stringstream retVal;
	if (data.atom.size() > 0) {
		if (data.type == Data::VERBATIM) {
			retVal << prefix << " = " << _analyzer->macroForLiteral(data.atom) << ";" << std::endl;
		} else {
			retVal << prefix << " = " << data.atom << ";" << std::endl;
		}
	} else if (data.compound.size() > 0) {
		for (std::map<std::string, Data>::const_iterator cIter = data.compound.begin(); cIter != data.compound.end(); cIter++) {
			retVal << dataToAssignments(prefix + "." + cIter->first, cIter->second);
		}
	} else if (data.array.size() > 0) {
		size_t index = 0;
		for(std::list<Data>::const_iterator aIter = data.array.begin(); aIter != data.array.end(); aIter++) {
			retVal << dataToAssignments(prefix + "[" + toStr(index) + "]", *aIter);
			index++;
		}
	}
	return retVal.str();
}

std::string ChartToPromela::sanitizeCode(const std::string& code) {
	std::string replaced = code;
	boost::replace_all(replaced, "\"", "'");
	boost::replace_all(replaced, "_sessionid", "_SESSIONID");
	boost::replace_all(replaced, "_name", "_NAME");
	return replaced;
}

std::string ChartToPromela::declForRange(const std::string& identifier, long minValue, long maxValue, bool nativeOnly) {
	//	return "int " + identifier; // just for testing

	// we know nothing about this type
	if (minValue == 0 && maxValue == 0)
		return "int " + identifier;

	if (minValue < 0) {
		// only short or int for negatives
		if (minValue < -32769 || maxValue > 32767)
			return "int " + identifier;
		return "short " + identifier;
	}

	// type is definitely positive
	if (nativeOnly) {
		if (maxValue > 32767)
			return "int " + identifier;
		if (maxValue > 255)
			return "short " + identifier;
		if (maxValue > 1)
			return "byte " + identifier;
		return "bool " + identifier;
	} else {
		return "unsigned " + identifier + " : " + toStr(BIT_WIDTH(maxValue));
	}
}

void ChartToPromela::writeDetermineShortestDelay(std::ostream& stream, int indent) {
	std::string padding;
	for (size_t i = 0; i < indent; i++) {
		padding += "  ";
	}

	stream << padding << "inline determineSmallestDelay(smallestDelay, queue) {" << std::endl;
	//    stream << padding << _analyzer->getTypeReset("tmpE", _analyzer->getType("_event"), "  ");
	stream << padding << "  if" << std::endl;
	stream << padding << "  :: len(queue) > 0 -> {" << std::endl;
	stream << padding << "    queue?<tmpE>;" << std::endl;
	stream << padding << "    if" << std::endl;
	stream << padding << "    :: (tmpE.delay < smallestDelay) -> { smallestDelay = tmpE.delay; }" << std::endl;
	stream << padding << "    :: else -> skip;" << std::endl;
	stream << padding << "    fi;" << std::endl;
	stream << padding << "  }" << std::endl;
	stream << padding << "  :: else -> skip;" << std::endl;
	stream << padding << "  fi;" << std::endl;
	stream << padding << "}" << std::endl;
}

void ChartToPromela::writeScheduleMachines(std::ostream& stream, int indent) {
	std::string padding;
	for (size_t i = 0; i < indent; i++) {
		padding += "  ";
	}

	stream << padding << "inline scheduleMachines() {" << std::endl;
	std::list<std::string> queues;
	queues.push_back("eQ");

	if (_allowEventInterleaving)
		queues.push_back("tmpQ");

	stream << "  /* schedule state-machines with regard to their event's delay */" << std::endl;
	stream << "  skip;" << std::endl;
	stream << "  d_step {" << std::endl;

	stream << std::endl << "/* determine smallest delay */" << std::endl;
	stream << "    int smallestDelay = 2147483647;" << std::endl;

	for (auto machine : *_machinesAll) {
		for (auto queue : queues) {
			stream << "    determineSmallestDelay(smallestDelay, " << machine.second->_prefix << queue << ");" << std::endl;
		}
	}

	TRACE_EXECUTION_V("Smallest delay is %d", "smallestDelay");

	stream << std::endl << "/* prioritize processes with lowest delay or internal events */" << std::endl;

	for (auto machine : *_machinesAll) {
		stream << "    rescheduleProcess(smallestDelay, "
		       << machine.second->_prefix << "procid, "
		       << machine.second->_prefix << "iQ, "
		       << machine.second->_prefix << "eQ";
		if (_allowEventInterleaving) {
			stream << ", " << machine.second->_prefix << "tmpQ);" << std::endl;
		} else {
			stream << ");" << std::endl;
		}
	}

	stream << std::endl << "/* advance time by subtracting the smallest delay from all event delays */" << std::endl;
	stream << "    if" << std::endl;
	stream << "    :: (smallestDelay > 0) -> {" << std::endl;
	for (auto machine : *_machinesAll) {
		for (auto queue : queues) {
			stream << "      advanceTime(smallestDelay, " << machine.second->_prefix << queue << ");" << std::endl;
		}
	}
	stream << "    }" << std::endl;
	stream << "    :: else -> skip;" << std::endl;
	stream << "    fi;" << std::endl;
	stream << "  }" << std::endl;
	stream << "  set_priority(_pid, 10);" << std::endl << std::endl;
	stream << padding << "}" << std::endl;
}

void ChartToPromela::writeAdvanceTime(std::ostream& stream, int indent) {
	std::string padding;
	for (size_t i = 0; i < indent; i++) {
		padding += "  ";
	}

	stream << padding << "inline advanceTime(increment, queue) {" << std::endl;
	stream << padding << "  tmpIndex = 0;" << std::endl;
	stream << padding << "  do" << std::endl;
	stream << padding << "  :: tmpIndex < len(queue) -> {" << std::endl;
	stream << padding << "    queue?tmpE;" << std::endl;
	stream << padding << "    if" << std::endl;
	stream << padding << "    :: tmpE.delay >= increment -> tmpE.delay = tmpE.delay - increment;" << std::endl;
	stream << padding << "    :: else -> skip;" << std::endl;
	stream << padding << "    fi" << std::endl;
	stream << padding << "    queue!tmpE;" << std::endl;
	stream << padding << "    tmpIndex++;" << std::endl;
	stream << padding << "  }" << std::endl;
	stream << padding << "  :: else -> break;" << std::endl;
	stream << padding << "  od" << std::endl;
	stream << padding << "}" << std::endl;
}

void ChartToPromela::writeInsertWithDelay(std::ostream& stream, int indent) {
	std::string padding;
	for (size_t i = 0; i < indent; i++) {
		padding += "  ";
	}

	uint32_t maxExternalQueueLength = 1;
	for(auto machine : *_machinesAll) {
		maxExternalQueueLength = MAX(maxExternalQueueLength, machine.second->_externalQueueLength);
	}

	maxExternalQueueLength += 6;

	if (maxExternalQueueLength <= 1) {
		stream << padding << "/* noop for external queues with length <= 1 */" << std::endl;
		stream << padding << "inline insertWithDelay(queue) {}" << std::endl;
	}

	stream << padding << "hidden _event_t _iwdQ[" << maxExternalQueueLength - 1 << "];" << std::endl;
	stream << padding << "hidden int _iwdQLength = 0;" << std::endl;
	stream << padding << "hidden int _iwdIdx1 = 0;" << std::endl;
	stream << padding << "hidden int _iwdIdx2 = 0;" << std::endl;
	stream << padding << "hidden _event_t _iwdTmpE;" << std::endl;
	stream << padding << "hidden _event_t _iwdLastE;" << std::endl;
	stream << padding << "bool _iwdInserted = false;" << std::endl;
	stream << padding << "" << std::endl;
	stream << padding << "/* last event in given queue is potentially at wrong position */" << std::endl;
	stream << padding << "inline insertWithDelay(queue) {" << std::endl;
	stream << padding << "  d_step {" << std::endl;
	stream << padding << "" << std::endl;
	stream << padding << "    /* only process for non-trivial queues */" << std::endl;
	stream << padding << "    if" << std::endl;
	stream << padding << "    :: len(queue) > 1 -> {" << std::endl;

	TRACE_EXECUTION("Reshuffling events")

	stream << padding << "" << std::endl;
	stream << padding << "      /* move all events but last over and remember the last one */" << std::endl;
	stream << padding << "      _iwdIdx1 = 0;" << std::endl;
	stream << padding << "      _iwdQLength = len(queue) - 1;" << std::endl;
	stream << padding << "" << std::endl;
	stream << padding << "      do" << std::endl;
	stream << padding << "      :: _iwdIdx1 < _iwdQLength -> {" << std::endl;
	stream << padding << "        queue?_iwdTmpE;" << std::endl;
	stream << padding << "        _iwdQ[_iwdIdx1].name = _iwdTmpE.name;" << std::endl;

	stream << _analyzer->getTypeAssignment("_iwdQ[_iwdIdx1]", "_iwdTmpE", _analyzer->getType("_event"), 8);

	stream << padding << "        _iwdIdx1++;" << std::endl;
	stream << padding << "      }" << std::endl;
	stream << padding << "      :: else -> break;" << std::endl;
	stream << padding << "      od" << std::endl;
	stream << padding << "" << std::endl;
	stream << padding << "      queue?_iwdLastE;" << std::endl;

	stream << padding << "" << std::endl;
	stream << padding << "      /* _iwdQ now contains all but last item in _iwdLastE */" << std::endl;
	stream << padding << "      assert(len(queue) == 0);" << std::endl;
	stream << padding << "" << std::endl;
	stream << padding << "      /* reinsert into queue and place _iwdLastE correctly */" << std::endl;
	stream << padding << "      _iwdInserted = false;" << std::endl;
	stream << padding << "      _iwdIdx2 = 0;" << std::endl;
	stream << padding << "" << std::endl;
	stream << padding << "      do" << std::endl;
	stream << padding << "      :: _iwdIdx2 < _iwdIdx1 -> {" << std::endl;
	stream << padding << "        _iwdTmpE.name = _iwdQ[_iwdIdx2].name;" << std::endl;

	stream << _analyzer->getTypeAssignment("_iwdTmpE", "_iwdQ[_iwdIdx2]", _analyzer->getType("_event"), 4);

	stream << padding << "" << std::endl;
	stream << padding << "        if" << std::endl;
	stream << padding << "        :: _iwdTmpE.delay > _iwdLastE.delay && !_iwdInserted -> {" << std::endl;
	stream << padding << "          queue!_iwdLastE;" << std::endl;
	TRACE_EXECUTION_V("Event %d has delay %d (last)", "_iwdLastE.name, _iwdLastE.delay");

	stream << padding << "          _iwdInserted = true;" << std::endl;
	stream << padding << "        }" << std::endl;
	stream << padding << "        :: else -> skip" << std::endl;
	stream << padding << "        fi;" << std::endl;
	stream << padding << "" << std::endl;
	stream << padding << "        queue!_iwdTmpE;" << std::endl;
	TRACE_EXECUTION_V("Event %d has delay %d", "_iwdTmpE.name, _iwdTmpE.delay");

	stream << padding << "        _iwdIdx2++;" << std::endl;
	stream << padding << "      }" << std::endl;
	stream << padding << "      :: else -> break;" << std::endl;
	stream << padding << "      od" << std::endl;
	stream << padding << "" << std::endl;
	stream << padding << "      if" << std::endl;
	stream << padding << "      :: !_iwdInserted -> {" << std::endl;
	stream << padding << "         queue!_iwdLastE;" << std::endl;
	TRACE_EXECUTION_V("Event %d has delay %d (last)", "_iwdLastE.name, _iwdLastE.delay");
	stream << padding << "      }" << std::endl;
	stream << padding << "      :: else -> skip;" << std::endl;
	stream << padding << "      fi;" << std::endl;
	stream << padding << "" << std::endl;
	stream << padding << "    }" << std::endl;
	stream << padding << "    :: else -> skip;" << std::endl;
	stream << padding << "    fi;" << std::endl;
	stream << padding << "  }" << std::endl;
	stream << padding << "}" << std::endl;
}

void ChartToPromela::writeRescheduleProcess(std::ostream& stream, int indent) {
	std::string padding;
	for (size_t i = 0; i < indent; i++) {
		padding += "  ";
	}

	if (_allowEventInterleaving) {
		stream << padding << "inline rescheduleProcess(smallestDelay, procId, internalQ, externalQ, tempQ) {" << std::endl;
	} else {
		stream << padding << "inline rescheduleProcess(smallestDelay, procId, internalQ, externalQ) {" << std::endl;
	}
	//    stream << _analyzer->getTypeReset("tmpE", _analyzer->getType("_event"), "      ");

	stream << padding << "  set_priority(procId, 1);" << std::endl;
	stream << padding << "  if" << std::endl;
	stream << padding << "  :: len(internalQ) > 0 -> set_priority(procId, 10);" << std::endl;
	stream << padding << "  :: else {" << std::endl;
	stream << padding << "    if" << std::endl;

	stream << padding << "    :: len(externalQ) > 0 -> {" << std::endl;
	stream << padding << "      externalQ?<tmpE>;" << std::endl;
	stream << padding << "      if" << std::endl;
	stream << padding << "      :: smallestDelay == tmpE.delay -> set_priority(procId, 10);" << std::endl;
	stream << padding << "      :: else -> skip;" << std::endl;
	stream << padding << "      fi;" << std::endl;
	stream << padding << "    }" << std::endl;

	if (_allowEventInterleaving) {
		stream << padding << "    :: len(tempQ) > 0 -> {" << std::endl;
		stream << padding << "      tempQ?<tmpE>;" << std::endl;
		stream << padding << "      if" << std::endl;
		stream << padding << "      :: smallestDelay == tmpE.delay -> set_priority(procId, 10);" << std::endl;
		stream << padding << "      :: else -> skip;" << std::endl;
		stream << padding << "      fi;" << std::endl;
		stream << padding << "    }" << std::endl;
	}

	stream << padding << "    :: else -> skip;" << std::endl;
	stream << padding << "    fi;" << std::endl;
	stream << padding << "  }" << std::endl;
	stream << padding << "  fi;" << std::endl;
	stream << padding << "}" << std::endl;
}

void ChartToPromela::writeCancelEvents(std::ostream& stream, int indent) {
	std::list<std::string> queues;
	queues.push_back("eQ");
	if (_allowEventInterleaving)
		queues.push_back("tmpQ");

	stream << "inline cancelSendId(sendIdentifier, source) {" << std::endl;
	for (auto machine : *_machinesAll) {
		for (auto queue : queues) {
			stream << "  cancelSendIdOnQueue(sendIdentifier, source, " << machine.second->_prefix << queue << ");" << std::endl;
		}
	}
	stream << "}" << std::endl;
	stream << std::endl;


	stream << "inline cancelSendIdOnQueue(sendIdentifier, source, queue) {" << std::endl;
	stream << "  tmpIndex = 0;" << std::endl;
	//    stream << _analyzer->getTypeReset("tmpE", _analyzer->getType("_event"), "  ");
	stream << "  do" << std::endl;
	stream << "  :: tmpIndex < len(queue) -> {" << std::endl;
	stream << "    queue?tmpE;" << std::endl;
	stream << "    if" << std::endl;
	stream << "    :: tmpE.sendid != sendIdentifier || tmpE.origin != source || tmpE.delay == 0 -> queue!tmpE;" << std::endl;
	stream << "    :: else -> skip;" << std::endl;
	stream << "    fi" << std::endl;
	stream << "    tmpIndex++;" << std::endl;
	stream << "  }" << std::endl;
	stream << "  :: else -> break;" << std::endl;
	stream << "  od" << std::endl;
	stream << "}" << std::endl;
}

void ChartToPromela::writeRemovePendingEventsFromInvoker(std::ostream& stream, int indent) {
	std::list<std::string> queues;
	queues.push_back("eQ");
	if (_allowEventInterleaving)
		queues.push_back("tmpQ");

	stream << "inline removePendingEventsFromInvoker(invoker) {" << std::endl;
	for (auto machine : *_machinesAll) {
		for (auto queue : queues) {
			stream << "  removePendingEventsFromInvokerOnQueue(invoker, " << machine.second->_prefix << queue << ");" << std::endl;
		}
	}
	stream << "}" << std::endl;
	stream << std::endl;

	stream << "inline removePendingEventsFromInvokerOnQueue(invoker, queue) {" << std::endl;
	stream << "  tmpIndex = len(queue);" << std::endl;
	//    stream << _analyzer->getTypeReset("tmpE", _analyzer->getType("_event"), "  ");
	stream << "  do" << std::endl;
	stream << "  :: tmpIndex > 0 -> {" << std::endl;
	stream << "    queue?tmpE;" << std::endl;
	stream << "    if" << std::endl;
	stream << "    :: false || ";
	if (_analyzer->usesEventField("delay"))
		stream << "tmpE.delay == 0 || ";
	if (_analyzer->usesEventField("invokeid"))
		stream << "tmpE.invokeid != invoker" << std::endl;
	stream << " -> {" << std::endl;

	TRACE_EXECUTION_V("Reenqueing event %d", "tmpE.name");

	stream << "      queue!tmpE;" << std::endl;
	stream << "    }" << std::endl;
	stream << "    :: else -> {" << std::endl;

	TRACE_EXECUTION_V("Dropping event %d", "tmpE.name");

	stream << "      skip;" << std::endl;
	stream << "    }" << std::endl;
	stream << "    fi" << std::endl;
	stream << "    tmpIndex = tmpIndex - 1;" << std::endl;
	stream << "  }" << std::endl;
	stream << "  :: else -> break;" << std::endl;
	stream << "  od" << std::endl;
	stream << "}" << std::endl;
}


}
