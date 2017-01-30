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

#define MAX_MACRO_CHARS 64

#include "PromelaCodeAnalyzer.h"
#include "uscxml/transform/ChartToPromela.h"
#include "uscxml/util/Predicates.h"
#include "uscxml/util/DOM.h"
#include "uscxml/util/String.h"

#include <boost/algorithm/string.hpp>

namespace uscxml {

using namespace XERCESC_NS;

void PromelaCodeAnalyzer::analyze(ChartToPromela* interpreter) {

	/**
	  Create macro names for state identifiers
	  Do not add as literals as they are not unique with nested state-charts
	 */
	{
		for (size_t i = 0; i < interpreter->_states.size(); i++) {
			DOMElement* state = interpreter->_states[i];
			if (HAS_ATTR(state, kXMLCharId)) {
				createMacroName(ATTR(state, kXMLCharId));
			}
		}
	}
//    _lastStrIndex = interpreter->_states.size();

	/** Find all event names that might occur */
	{
		std::list<XERCESC_NS::DOMElement*> internalEventNames = DOMUtils::inDocumentOrder({
			XML_PREFIX(interpreter->_scxml).str() + "transition",
			XML_PREFIX(interpreter->_scxml).str() + "raise",
			XML_PREFIX(interpreter->_scxml).str() + "send"
		}, interpreter->_scxml);

		for (auto internalEventName : internalEventNames) {
			if (HAS_ATTR_CAST(internalEventName, kXMLCharEvent)) {
				std::string eventNames = ATTR_CAST(internalEventName, kXMLCharEvent);
				std::list<std::string> events = tokenize(eventNames);
				for (std::list<std::string>::iterator eventIter = events.begin();
				        eventIter != events.end(); eventIter++) {
					std::string eventName = *eventIter;
					if (boost::ends_with(eventName, "*"))
						eventName = eventName.substr(0, eventName.size() - 1);
					if (boost::ends_with(eventName, "."))
						eventName = eventName.substr(0, eventName.size() - 1);
					if (eventName.size() > 0)
						addEvent(eventName);
				}
			}
		}

		for (auto state : interpreter->_states) {
			if (HAS_ATTR(state, kXMLCharId) && (isCompound(state) || isParallel(state))) {
				addEvent("done.state." + ATTR(state, kXMLCharId));
			}
		}

		std::list<XERCESC_NS::DOMElement*> invokers = DOMUtils::inDocumentOrder({XML_PREFIX(interpreter->_scxml).str() + "invoke"}, interpreter->_scxml, false);
		for (auto invoker : invokers) {
			addCode("_event.invokeid", interpreter);

			if (HAS_ATTR(invoker, kXMLCharId)) {
				addEvent("done.state." + ATTR(invoker, kXMLCharId));
			}
		}
	}

	// add event names from trie to string literals
	std::list<TrieNode*> events = _eventTrie.getWordsWithPrefix("");
	for (auto event : events) {
		addLiteral(event->value);
	}


	/** Find all string literals */
	{
		// string literals for raise / send content
		std::list<XERCESC_NS::DOMElement*> contents = DOMUtils::inDocumentOrder({
			XML_PREFIX(interpreter->_scxml).str() + "content"
		}, interpreter->_scxml);

		for (auto content : contents) {
			if (!content->hasChildNodes())
				continue;
			std::string contentStr = spaceNormalize(X(content->getFirstChild()->getNodeValue()));
			if (!isNumeric(contentStr.c_str(), 10)) {
				addLiteral(contentStr);
			}
		}
	}

	/* add platform variables as string literals */
	addLiteral(interpreter->_prefix + "_sessionid");
	addLiteral(interpreter->_prefix + "_name");


	/** Extract and analyze source code */
	{
		std::list<XERCESC_NS::DOMElement*> withCond = DOMUtils::inDocumentOrder({
			XML_PREFIX(interpreter->_scxml).str() + "transition",
			XML_PREFIX(interpreter->_scxml).str() + "if",
			XML_PREFIX(interpreter->_scxml).str() + "elseif"
		}, interpreter->_scxml);

		for (auto cond : withCond) {
			if (HAS_ATTR(cond, kXMLCharCond)) {
				std::string code = ATTR_CAST(cond, kXMLCharCond);
				code = sanitizeCode(code);
				addCode(code, interpreter);
				cond->setAttribute(X("cond"), X(code));
			}
		}

		std::list<XERCESC_NS::DOMElement*> withExpr = DOMUtils::inDocumentOrder({
			XML_PREFIX(interpreter->_scxml).str() + "log",
			XML_PREFIX(interpreter->_scxml).str() + "data",
			XML_PREFIX(interpreter->_scxml).str() + "assign",
			XML_PREFIX(interpreter->_scxml).str() + "content",
			XML_PREFIX(interpreter->_scxml).str() + "param"
		}, interpreter->_scxml);

		for (auto expr : withExpr) {
			if (HAS_ATTR(expr, kXMLCharExpr)) {
				std::string code = ATTR_CAST(expr, kXMLCharExpr);
				code = sanitizeCode(code);
				addCode(code, interpreter);
				expr->setAttribute(X("expr"), X(code));
			}
		}

		std::list<XERCESC_NS::DOMElement*> withLocation = DOMUtils::inDocumentOrder({
			XML_PREFIX(interpreter->_scxml).str() + "assign"
		}, interpreter->_scxml);

		for (auto location : withLocation) {
			if (HAS_ATTR(location, kXMLCharLocation)) {
				std::string code = ATTR_CAST(location, kXMLCharLocation);
				code = sanitizeCode(code);
				addCode(code, interpreter);
				location->setAttribute(X("location"), X(code));
			}
		}

		std::list<XERCESC_NS::DOMElement*> withText = DOMUtils::inDocumentOrder({
			XML_PREFIX(interpreter->_scxml).str() + "script"
		}, interpreter->_scxml);

		for (auto text : withText) {
			std::list<XERCESC_NS::DOMNode*> texts = DOMUtils::filterChildType(DOMNode::TEXT_NODE, text, true);
			for (auto textBlock : texts) {
				DOMText* textText = static_cast<DOMText*>(textBlock);
				std::string code = X(textText->getNodeValue()).str();
				if (code.size() > 0) {
					code = sanitizeCode(code);
					addCode(code, interpreter);
					textText->setNodeValue(X(code));
				}
			}
		}

		std::list<XERCESC_NS::DOMElement*> foreachs = DOMUtils::inDocumentOrder({
			XML_PREFIX(interpreter->_scxml).str() + "foreach"
		}, interpreter->_scxml);

		for (auto foreach : foreachs) {
				if (HAS_ATTR(foreach, kXMLCharIndex)) {
					addCode(ATTR(foreach, kXMLCharIndex), interpreter);
				} else {
					_hasIndexLessLoops = true;
				}
				if (HAS_ATTR(foreach, kXMLCharItem)) {
					addCode(ATTR(foreach, kXMLCharItem), interpreter);
				}
			}

		// do we need sendid / invokeid?
		{
			std::list<DOMElement*> invokes = DOMUtils::inDocumentOrder({XML_PREFIX(interpreter->_scxml).str() + "invoke"}, interpreter->_scxml);
			std::list<DOMElement*> sends = DOMUtils::inDocumentOrder({XML_PREFIX(interpreter->_scxml).str() + "send"}, interpreter->_scxml);
			std::list<DOMElement*> cancels = DOMUtils::inDocumentOrder({XML_PREFIX(interpreter->_scxml).str() + "cancel"}, interpreter->_scxml);

			if (cancels.size() > 0) {
				addCode("_event.origin", interpreter);
				_usesCancel = true;
			}

			for (auto send : sends) {
				if (HAS_ATTR(send, kXMLCharIdLocation)) {
					addCode("_event.sendid", interpreter);
				}
				if (HAS_ATTR(send, kXMLCharId)) {
					addLiteral(ATTR(send, kXMLCharId));
					addCode("_event.sendid", interpreter);
				}

				// do we need delays?
				if (HAS_ATTR(send, kXMLCharDelay) || HAS_ATTR(send, kXMLCharDelayExpr)) {
					size_t delay = strTo<size_t>(ATTR(send, kXMLCharDelay));
					if (delay > largestDelay)
						largestDelay = delay;
					addCode("_event.delay", interpreter);
#if NEW_DELAY_RESHUFFLE
#else
					addCode("_event.seqNr", interpreter);
#endif
				}
			}
		}

		// add all namelist entries to the _event structure
		{
			std::list<DOMElement*> withNamelists;
			withNamelists.splice(withNamelists.end(), DOMUtils::inDocumentOrder({XML_PREFIX(interpreter->_scxml).str() + "send"}, interpreter->_scxml));
			withNamelists.splice(withNamelists.end(), DOMUtils::inDocumentOrder({XML_PREFIX(interpreter->_scxml).str() + "invoke"}, interpreter->_scxml));
			for (auto withNamelist : withNamelists) {
				if (HAS_ATTR(withNamelist, kXMLCharNameList)) {
					std::string namelist = ATTR(withNamelist, kXMLCharNameList);
					std::list<std::string> names = tokenize(namelist);
					for (std::list<std::string>::iterator nameIter = names.begin(); nameIter != names.end(); nameIter++) {
						addCode("_event.data." + *nameIter + " = 0;", interpreter); // introduce for _event_t typedef
					}
				}
			}
		}

	}

}

void PromelaCodeAnalyzer::addEvent(const std::string& eventName) {
	addLiteral(eventName);
	_eventTrie.addWord(eventName);
}

std::string PromelaCodeAnalyzer::sanitizeCode(const std::string& code) {
	std::string replaced = code;
	boost::replace_all(replaced, "\"", "'");
	boost::replace_all(replaced, "_sessionid", "_SESSIONID");
	boost::replace_all(replaced, "_name", "_NAME");
	return replaced;
}

void PromelaCodeAnalyzer::addCode(const std::string& code, ChartToPromela* interpreter) {
	PromelaParser parser(code);
	//	parser.dump();

	// find all strings
	std::list<PromelaParserNode*> astNodes;
	astNodes.push_back(parser.ast);

	while(astNodes.size() > 0) {
		PromelaParserNode* node = astNodes.front();
		astNodes.pop_front();

		//		node->dump();

		bool hasValue = false;
		int assignedValue = 0;


		switch (node->type) {
		case PML_STRING: {
			std::string unquoted = node->value;
			if (boost::starts_with(unquoted, "'")) {
				unquoted = unquoted.substr(1, unquoted.size() - 2);
			}
			addLiteral(unquoted);
			break;
		}
		case PML_ASGN:
			if (node->operands.back()->type == PML_CONST) {
				hasValue = true;
				if (isInteger(node->operands.back()->value.c_str(), 10)) {
					assignedValue = strTo<int>(node->operands.back()->value);
				}
			}
			if (node->operands.back()->type == PML_STRING) {
				// remember strings for later
				astNodes.push_back(node->operands.back());
			}
			if (node->operands.front()->type == PML_CMPND) {
				node = node->operands.front();
			} else {
				break;
			}
		//			if (node->operands.front()->type != PML_NAME)
		//				break; // this will skip array assignments
		case PML_CMPND: {
			std::string nameOfType;
			std::list<PromelaParserNode*>::iterator opIter = node->operands.begin();
			if ((*opIter)->type != PML_NAME) {
				node->dump();
				return;
				assert(false);
			}

			PromelaTypedef* td = &_typeDefs;
			std::string seperator;

			while(opIter != node->operands.end()) {
				switch ((*opIter)->type) {
				case PML_NAME:
					td = &td->types[(*opIter)->value];
					td->occurrences.insert(interpreter);

					nameOfType += seperator + (*opIter)->value;
					if (nameOfType.compare("_x") == 0)
						_usesPlatformVars = true;
					seperator = "_";
					td->name = nameOfType + "_t";
					break;
				case PML_VAR_ARRAY: {
					PromelaParserNode* name = (*opIter)->operands.front();
					PromelaParserNode* subscript = *(++(*opIter)->operands.begin());
					td = &td->types[name->value];
					td->occurrences.insert(interpreter);

					nameOfType += seperator + name->value;
					td->name = nameOfType + "_t";

					if (isInteger(subscript->value.c_str(), 10)) {
						td->arraySize = strTo<int>(subscript->value);
					}
					break;
				}
				default:
					if ((*opIter)->type == PML_CONST) {
						// break fall through from ASGN
						break;
					}
					//					node->dump();
					//					assert(false);
					break;
				}

				if (nameOfType.compare("_x_states") == 0) {
					_usesInPredicate = true;
				}
				if (nameOfType.compare("_event_type") == 0) {
					addLiteral("internal");
					addLiteral("external");
					addLiteral("platform");
				}
				if (nameOfType.compare("_event_origintype") == 0) {
					addLiteral("http://www.w3.org/TR/scxml/#SCXMLEventProcessor");
				}
				opIter++;
			}

			if (hasValue) {
				if (td->maxValue < assignedValue)
					td->maxValue = assignedValue;
				if (td->minValue > assignedValue)
					td->minValue = assignedValue;
			}

			continue; // skip processing nested AST nodes
		}
		case PML_NAME: {
			_typeDefs.types[node->value].occurrences.insert(interpreter);
			_typeDefs.types[node->value].minValue = 0;
			_typeDefs.types[node->value].maxValue = 0;
			// test325
			if (node->value.compare("_ioprocessors") == 0) {
				addCode("_ioprocessors.scxml.location", interpreter);
			}

			break;
		}

		default:
			//			node->dump();
			break;
			//				assert(false);
		}

		astNodes.insert(astNodes.end(), node->operands.begin(), node->operands.end());

	}
}

void PromelaCodeAnalyzer::addLiteral(const std::string& literal, int forceIndex) {
	if (boost::starts_with(literal, "'"))
		throw std::runtime_error("Literal " + literal + " passed with quotes");

	if (_literals.find(literal) != _literals.end())
		return;
	_literals.insert(literal);
	createMacroName(literal);
	enumerateLiteral(literal, forceIndex);
}

int PromelaCodeAnalyzer::indexForLiteral(const std::string& literal) {
	if (boost::starts_with(literal, "'"))
		throw std::runtime_error("Literal " + literal + " passed with quotes");

	if (_strIndex.find(literal) == _strIndex.end())
		throw std::runtime_error("No index for literal " + literal + " known");
	return _strIndex[literal];
}

std::string PromelaCodeAnalyzer::macroForLiteral(const std::string& literal) {
	if (boost::starts_with(literal, "'"))
		throw std::runtime_error("Literal " + literal + " passed with quotes");

	if (_strMacros.find(literal) == _strMacros.end())
		throw std::runtime_error("No macro for literal '" + literal + "' known");
	return _strMacros[literal];
}


std::string PromelaCodeAnalyzer::createMacroName(const std::string& literal) {
	if (_strMacros.find(literal) != _strMacros.end())
		return _strMacros[literal];

	// find a suitable macro name for the strings
	std::string macroName = literal; //literal.substr(1, literal.size() - 2);

	// cannot start with digit
	if (isInteger(macroName.substr(0,1).c_str(), 10))
		macroName = "_" + macroName;

	macroName = macroName.substr(0, MAX_MACRO_CHARS);
	boost::to_upper(macroName);

	std::string illegalChars = "#\\/:?\"<>| \n\t()[]{}',.-";
	std::string tmp;
	std::string::iterator it = macroName.begin();
	while (it < macroName.end()) {
		bool found = illegalChars.find(*it) != std::string::npos;
		if(found) {
			tmp += '_';
			it++;
			while(it < macroName.end() && illegalChars.find(*it) != std::string::npos) {
				it++;
			}
		} else {
			tmp += *it++;
		}
	}
	macroName = tmp;
	if(macroName.length() < 1)
		macroName = "_EMPTY_STRING";
	if(macroName.length() < 2 && macroName[0] == '_')
		macroName = "_WEIRD_CHARS";

	unsigned int index = 2;
	while (_macroNameSet.find(macroName) != _macroNameSet.end()) {
		std::string suffix = toStr(index);
		if (macroName.size() > suffix.size()) {
			macroName = macroName.substr(0, macroName.size() - suffix.size()) + suffix;
		} else {
			macroName = suffix;
		}
		index++;
	}

	_macroNameSet.insert(macroName);
	_strMacros[literal] = macroName;
	return macroName;
}

int PromelaCodeAnalyzer::enumerateLiteral(const std::string& literal, int forceIndex) {
	if (forceIndex >= 0) {
		_strIndex[literal] = forceIndex;
		return forceIndex;
	}

	if (_strIndex.find(literal) != _strIndex.end())
		return _strIndex[literal];

	_strIndex[literal] = _lastStrIndex++;
	return _lastStrIndex + 1;
}

std::string PromelaCodeAnalyzer::adaptCode(const std::string& code, const std::string& prefix) {
	//	for (std::map<std::string, std::string>::const_iterator litIter = _strMacros.begin(); litIter != _strMacros.end(); litIter++) {
	//		boost::replace_all(replaced, "'" + litIter->first + "'", litIter->second);
	//	}
	//	boost::replace_all(replaced, "_event", prefix + "_event");
	// replace all variables from analyzer

	std::string processed = code;
	std::stringstream processedStr;
	std::list<std::pair<size_t, size_t> > posList;
	std::list<std::pair<size_t, size_t> >::iterator posIter;
	size_t lastPos;

	// prepend all identifiers with our prefix
	{
		PromelaParser parsed(processed);
		//		parsed.dump();
		posList = getTokenPositions(code, PML_NAME, parsed.ast);
		posList.sort();
		posIter = posList.begin();
		lastPos = 0;

		while (posIter != posList.end()) {
			std::string token = code.substr(posIter->first, posIter->second - posIter->first);
			if (std::all_of(token.begin(), token.end(), ::isupper) && false) {
				// assume it is a state-name macro
				processedStr << code.substr(lastPos, posIter->first - lastPos) << token;
			} else if (boost::starts_with(prefix, token)) {
				processedStr << code.substr(lastPos, posIter->first - lastPos) << token;
			} else {
				processedStr << code.substr(lastPos, posIter->first - lastPos) << prefix << token;
			}
			lastPos = posIter->second;
			posIter++;
		}
		processedStr << processed.substr(lastPos, processed.size() - lastPos);

		processed = processedStr.str();
		processedStr.clear();
		processedStr.str("");
	}

	// replace string literals
	{
		PromelaParser parsed(processed);
		posList = getTokenPositions(code, PML_STRING, parsed.ast);
		posList.sort();
		posIter = posList.begin();
		lastPos = 0;

		while (posIter != posList.end()) {
			processedStr << processed.substr(lastPos, posIter->first - lastPos);
			//			std::cout << processed.substr(posIter->first + 1, posIter->second - posIter->first - 2) << std::endl;
			assert(_strMacros.find(processed.substr(posIter->first + 1, posIter->second - posIter->first - 2)) != _strMacros.end());
			processedStr << _strMacros[processed.substr(posIter->first + 1, posIter->second - posIter->first - 2)];
			lastPos = posIter->second;
			posIter++;
		}
		processedStr << processed.substr(lastPos, processed.size() - lastPos);

		processed = processedStr.str();
		processedStr.clear();
		processedStr.str("");
	}

	return processed;
}

std::list<std::pair<size_t, size_t> > PromelaCodeAnalyzer::getTokenPositions(const std::string& expr, int type, PromelaParserNode* ast) {
	std::list<std::pair<size_t, size_t> > posList;
	if (ast->type == type && ast->loc != NULL) {
		//		ast->dump();
		if (type == PML_NAME && ast->parent &&
		        ((ast->parent->type == PML_CMPND && ast->parent->operands.front() != ast) ||
		         (ast->parent->parent && ast->parent->type == PML_VAR_ARRAY && ast->parent->parent->type == PML_CMPND))) {
			// field in a compound
		} else {
			if (ast->loc->firstLine == 0) {
				posList.push_back(std::make_pair(ast->loc->firstCol, ast->loc->lastCol));
			} else {
				int line = ast->loc->firstLine;
				size_t lastPos = 0;
				while(line > 0) {
					lastPos = expr.find_first_of('\n', lastPos + 1);
					line--;
				}
				posList.push_back(std::make_pair(lastPos + ast->loc->firstCol, lastPos + ast->loc->lastCol));
			}
		}
	}
	for (std::list<PromelaParserNode*>::iterator opIter = ast->operands.begin(); opIter != ast->operands.end(); opIter++) {
		std::list<std::pair<size_t, size_t> > tmp = getTokenPositions(expr, type, *opIter);
		posList.insert(posList.end(), tmp.begin(), tmp.end());
	}
	return posList;
}

std::string PromelaCodeAnalyzer::getTypeReset(const std::string& var, const PromelaTypedef& type, size_t indent) {
	std::stringstream assignment;
	std::string padding;
	for (size_t i = 0; i < indent; i++)
		padding += "  ";

	std::map<std::string, PromelaTypedef>::const_iterator typeIter = type.types.begin();
	while(typeIter != type.types.end()) {
		const PromelaTypedef& innerType = typeIter->second;
		if (innerType.arraySize > 0) {
			for (size_t i = 0; i < innerType.arraySize; i++) {
				assignment << padding << var << "." << typeIter->first << "[" << i << "] = 0;" << std::endl;
			}
		} else if (innerType.types.size() > 0) {
			assignment << getTypeReset(var + "." + typeIter->first, typeIter->second, indent);
		} else {
			assignment << padding << var << "." << typeIter->first << " = 0;" << std::endl;
		}
		typeIter++;
	}
	return assignment.str();

}

std::string PromelaCodeAnalyzer::getTypeAssignment(const std::string& varTo, const std::string& varFrom, const PromelaTypedef& type, size_t indent) {
	std::stringstream assignment;
	std::string padding;
	for (size_t i = 0; i < indent; i++)
		padding += "  ";

	std::map<std::string, PromelaTypedef>::const_iterator typeIter = type.types.begin();
	while(typeIter != type.types.end()) {
		const PromelaTypedef& innerType = typeIter->second;
		if (innerType.arraySize > 0) {
			for (size_t i = 0; i < innerType.arraySize; i++) {
				assignment << padding << varTo << "." << typeIter->first << "[" << i << "] = " << varFrom << "." << typeIter->first << "[" << i << "];" << std::endl;
			}
		} else if (innerType.types.size() > 0) {
			assignment << getTypeAssignment(varTo + "." + typeIter->first, varFrom + "." + typeIter->first, typeIter->second, indent);
		} else {
			assignment << padding << varTo << "." << typeIter->first << " = " << varFrom << "." << typeIter->first << ";" << std::endl;
		}
		typeIter++;
	}
	return assignment.str();
}

}
