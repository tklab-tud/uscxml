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

#include "uscxml/transform/ChartToFSM.h"
#include "uscxml/transform/FSMToPromela.h"
#include "uscxml/transform/FlatStateIdentifier.h"
#include "uscxml/plugins/datamodel/promela/PromelaParser.h"
#include "uscxml/plugins/datamodel/promela/parser/promela.tab.hpp"

#include <DOM/io/Stream.hpp>
#include <iostream>
#include "uscxml/UUID.h"
#include <math.h>
#include <boost/algorithm/string.hpp>
#include <glog/logging.h>

#define MAX_MACRO_CHARS 64
#define MIN_COMMENT_PADDING 60

#define BIT_WIDTH(number) (number > 1 ? (int)ceil(log((double)number) / log((double)2.0)) : 1)

#define INDENT_MIN(stream, start, cols) \
for (int indentIndex = start; indentIndex < cols; indentIndex++) \
	stream << " ";

namespace uscxml {

using namespace Arabica::DOM;
using namespace Arabica::XPath;

void FSMToPromela::writeProgram(std::ostream& stream,
                                const Interpreter& interpreter) {
	FSMToPromela promelaWriter;
	interpreter.getImpl()->copyTo(&promelaWriter);
	promelaWriter.writeProgram(stream);
}

FSMToPromela::FSMToPromela() {
}

void PromelaEventSource::writeStartEventSources(std::ostream& stream, int indent) {
	std::string padding;
	for (int i = 0; i < indent; i++) {
		padding += "  ";
	}

	std::list<PromelaInline>::iterator sourceIter = eventSources.inlines.begin();
	int i = 0;
	while(sourceIter != eventSources.inlines.end()) {
		if (sourceIter->type != PromelaInline::PROMELA_EVENT_SOURCE_CUSTOM && sourceIter->type != PromelaInline::PROMELA_EVENT_SOURCE) {
			sourceIter++;
			continue;
		}
		std::string sourceName = name + "_"+ toStr(i);
		stream << padding << "run " << sourceName << "EventSource();" << std::endl;

		i++;
		sourceIter++;
	}

}

void PromelaEventSource::writeStopEventSources(std::ostream& stream, int indent) {
	std::string padding;
	for (int i = 0; i < indent; i++) {
		padding += "  ";
	}

	std::list<PromelaInline>::iterator sourceIter = eventSources.inlines.begin();
	int i = 0;
	while(sourceIter != eventSources.inlines.end()) {
		if (sourceIter->type != PromelaInline::PROMELA_EVENT_SOURCE_CUSTOM && sourceIter->type != PromelaInline::PROMELA_EVENT_SOURCE) {
			sourceIter++;
			continue;
		}
		std::string sourceName = name + "_"+ toStr(i);
		stream << padding << sourceName << "EventSourceDone = 1;" << std::endl;

		i++;
		sourceIter++;
	}

}

void PromelaEventSource::writeDeclarations(std::ostream& stream, int indent) {
	std::string padding;
	for (int i = 0; i < indent; i++) {
		padding += "  ";
	}

	std::list<PromelaInline>::iterator sourceIter = eventSources.inlines.begin();
	int i = 0;
	while(sourceIter != eventSources.inlines.end()) {
		if (sourceIter->type != PromelaInline::PROMELA_EVENT_SOURCE_CUSTOM && sourceIter->type != PromelaInline::PROMELA_EVENT_SOURCE) {
			sourceIter++;
			continue;
		}
		std::string sourceName = name + "_"+ toStr(i);
		stream << "bool " << sourceName << "EventSourceDone = 0;" << std::endl;

		i++;
		sourceIter++;
	}
}

void PromelaEventSource::writeEventSource(std::ostream& stream) {

	std::list<PromelaInline>::iterator sourceIter = eventSources.inlines.begin();
	int i = 0;
	while(sourceIter != eventSources.inlines.end()) {
		if (sourceIter->type != PromelaInline::PROMELA_EVENT_SOURCE_CUSTOM && sourceIter->type != PromelaInline::PROMELA_EVENT_SOURCE) {
			sourceIter++;
			continue;
		}

		std::string sourceName = name + "_"+ toStr(i);

		stream << "proctype " << sourceName << "EventSource() {" << std::endl;
		stream << "  " << sourceName << "EventSourceDone = 0;" << std::endl;
		stream << "  " << sourceName << "NewEvent:" << std::endl;
		stream << "  " << "if" << std::endl;
		stream << "  " << ":: " << sourceName << "EventSourceDone -> skip;" << std::endl;
		stream << "  " << ":: else { " << std::endl;

		Trie& trie = analyzer->getTrie();

		if (sourceIter->type == PromelaInline::PROMELA_EVENT_SOURCE_CUSTOM) {
			std::string content = sourceIter->content;

			boost::replace_all(content, "#REDO#", sourceName + "NewEvent");
			boost::replace_all(content, "#DONE#", sourceName + "Done");

			std::list<TrieNode*> eventNames = trie.getChildsWithWords(trie.getNodeWithPrefix(""));
			std::list<TrieNode*>::iterator eventNameIter = eventNames.begin();
			while(eventNameIter != eventNames.end()) {
				boost::replace_all(content, "#" + (*eventNameIter)->value + "#", (*eventNameIter)->identifier);
				eventNameIter++;
			}

			stream << FSMToPromela::beautifyIndentation(content, 2) << std::endl;

		} else {
			stream << "  " << "  if" << std::endl;
//			stream << "  " << "  :: 1 -> " << "goto " << sourceName << "NewEvent;" << std::endl;

			std::list<std::list<std::string> >::const_iterator seqIter = sourceIter->sequences.begin();
			while(seqIter != sourceIter->sequences.end()) {
				stream << "    " << ":: ";
				std::list<std::string>::const_iterator evIter = seqIter->begin();
				while(evIter != seqIter->end()) {
					TrieNode* node = trie.getNodeWithPrefix(*evIter);
					stream << "eQ!" << node->identifier << "; ";
					evIter++;
				}
				stream << "goto " << sourceName << "NewEvent;" << std::endl;
				seqIter++;
			}

			stream << "  " << "  fi;" << std::endl;
		}

		stream << "  " << "}" << std::endl;
		stream << "  " << "fi;" << std::endl;
		stream << sourceName << "Done:" << " skip;" << std::endl;
		stream << "}" << std::endl;

		i++;
		sourceIter++;
	}
}

PromelaEventSource::PromelaEventSource() {
	type = PROMELA_EVENT_SOURCE_INVALID;
	analyzer = NULL;
}

PromelaEventSource::PromelaEventSource(const PromelaInlines& sources, const Arabica::DOM::Node<std::string>& parent) {
	type = PROMELA_EVENT_SOURCE_INVALID;
	analyzer = NULL;

	eventSources = sources;
	container = parent;
}

void PromelaCodeAnalyzer::addCode(const std::string& code) {
	PromelaParser parser(code);

	// find all strings
	std::list<PromelaParserNode*> astNodes;
	astNodes.push_back(parser.ast);

	while(astNodes.size() > 0) {
		PromelaParserNode* node = astNodes.front();
		astNodes.pop_front();

		switch (node->type) {
		case PML_STRING: {
			std::string unquoted = node->value;
			if (boost::starts_with(unquoted, "'")) {
				unquoted = unquoted.substr(1, unquoted.size() - 2);
			}
			addLiteral(unquoted);
			break;
		}
		case PML_CMPND: {
			std::string nameOfType;
			std::list<PromelaParserNode*>::iterator opIter = node->operands.begin();
			assert((*opIter)->type == PML_NAME);

			PromelaTypedef* td = &_typeDefs;
			std::string seperator;

			while(opIter != node->operands.end()) {
				switch ((*opIter)->type) {
				case PML_NAME:
					td = &td->types[(*opIter)->value];
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
					nameOfType += seperator + name->value;
					td->name = nameOfType + "_t";

					if (isInteger(subscript->value.c_str(), 10)) {
						td->arraySize = strTo<int>(subscript->value);
					}
					break;
				}
				default:
					node->dump();
					assert(false);
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
			break;
		}
		case PML_NAME: {
		}
		default:
			break;
//				node->dump();
//				assert(false);
		}

		astNodes.merge(node->operands);
	}
}

void PromelaCodeAnalyzer::addEvent(const std::string& eventName) {
	if (_events.find(eventName) != _events.end())
		return;

	addLiteral(eventName, _lastEventIndex);
	assert(_strIndex.find(eventName) != _strIndex.end());

	_eventTrie.addWord(eventName);
	_events[eventName] = _strIndex[eventName];
	_lastEventIndex++;
}

void PromelaCodeAnalyzer::addState(const std::string& stateName) {
	if (_states.find(stateName) != _states.end())
		return;

	createMacroName(stateName);

//	addLiteral(stateName);
//	_states[stateName] = enumerateLiteral(stateName);
	if (_origStateMap.find(stateName) == _origStateMap.end()) {
		FlatStateIdentifier flatId(stateName);
		_origStateMap[stateName] = flatId.getActive();
		for (std::list<std::string>::iterator origIter = _origStateMap[stateName].begin(); origIter != _origStateMap[stateName].end(); origIter++) {
			//addLiteral(*origIter); // add original state names as string literals
			if (_origStateIndex.find(*origIter) == _origStateIndex.end()) {
				_origStateIndex[*origIter] = _lastStateIndex++;
				createMacroName(*origIter);
			}
		}
	}
}

int PromelaCodeAnalyzer::arrayIndexForOrigState(const std::string& stateName) {
	if (_origStateIndex.find(stateName) == _origStateIndex.end())
		throw std::runtime_error("No original state " + stateName + " known");
	return _origStateIndex[stateName];
}

void PromelaCodeAnalyzer::addLiteral(const std::string& literal, int forceIndex) {
	if (boost::starts_with(literal, "'"))
		throw std::runtime_error("Literal " + literal + " passed with quotes");

	if (_strLiterals.find(literal) != _strLiterals.end())
		return;

	_strLiterals.insert(literal);
	createMacroName(literal);
	enumerateLiteral(literal, forceIndex);
}

int PromelaCodeAnalyzer::enumerateLiteral(const std::string& literal, int forceIndex) {
	if (forceIndex >= 0) {
		_strIndex[literal] = forceIndex;
		return forceIndex;
	}

	if (_strIndex.find(literal) != _strIndex.end())
		return _strIndex[literal];

	_strIndex[literal] = ++_lastStrIndex;
	return _lastStrIndex + 1;
}

std::string PromelaCodeAnalyzer::createMacroName(const std::string& literal) {
	if (_strMacroNames.find(literal) != _strMacroNames.end())
		return _strMacroNames[literal];

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
	_strMacroNames[literal] = macroName;
	return macroName;
}

std::string PromelaCodeAnalyzer::macroForLiteral(const std::string& literal) {
	if (boost::starts_with(literal, "'"))
		throw std::runtime_error("Literal " + literal + " passed with quotes");

	if (_strMacroNames.find(literal) == _strMacroNames.end())
		throw std::runtime_error("No macro for literal " + literal + " known");
	return _strMacroNames[literal];
}

int PromelaCodeAnalyzer::indexForLiteral(const std::string& literal) {
	if (boost::starts_with(literal, "'"))
		throw std::runtime_error("Literal " + literal + " passed with quotes");

	if (_strIndex.find(literal) == _strIndex.end())
		throw std::runtime_error("No index for literal " + literal + " known");
	return _strIndex[literal];
}

std::string PromelaCodeAnalyzer::replaceLiterals(const std::string code) {
	std::string replaced = code;
	for (std::map<std::string, std::string>::const_iterator litIter = _strMacroNames.begin(); litIter != _strMacroNames.end(); litIter++) {
		boost::replace_all(replaced, "'" + litIter->first + "'", litIter->second);
	}
	return replaced;
}

std::set<std::string> PromelaCodeAnalyzer::getEventsWithPrefix(const std::string& prefix) {
	std::set<std::string> eventNames;
	std::list<TrieNode*> trieNodes = _eventTrie.getWordsWithPrefix(prefix);

	std::list<TrieNode*>::iterator trieIter = trieNodes.begin();
	while(trieIter != trieNodes.end()) {
		eventNames.insert((*trieIter)->value);
		trieIter++;
	}

	return eventNames;
}


void FSMToPromela::writeEvents(std::ostream& stream) {
	std::map<std::string, int> events = _analyzer.getEvents();
	std::map<std::string, int>::iterator eventIter = events.begin();
	stream << "/* event name identifiers */" << std::endl;
	while(eventIter != events.end()) {
		if (eventIter->first.length() > 0) {
			stream << "#define " << _analyzer.macroForLiteral(eventIter->first) << " " << _analyzer.indexForLiteral(eventIter->first);
			stream << " /* from \"" << eventIter->first << "\" */" << std::endl;
		}
		eventIter++;
	}
}

void FSMToPromela::writeStates(std::ostream& stream) {
	stream << "/* state name identifiers */" << std::endl;
	for (int i = 0; i < _globalStates.size(); i++) {
		stream << "#define " << "s" << i << " " << i;
		stream << " /* from \"" << ATTR_CAST(_globalStates[i], "id") << "\" */" << std::endl;
	}
}

void FSMToPromela::writeStateMap(std::ostream& stream) {
	stream << "/* macros for original state names */" << std::endl;
	std::map<std::string, int> origStates = _analyzer.getOrigStates();
	for (std::map<std::string, int>::iterator origIter = origStates.begin(); origIter != origStates.end(); origIter++) {
		stream << "#define " << _analyzer.macroForLiteral(origIter->first) << " " << origIter->second;
		stream << " /* from \"" << origIter->first << "\" */" << std::endl;
	}

//	std::map<std::string, int> states = _analyzer.getStates();
//	size_t stateIndex = 0;
//	for (std::map<std::string, int>::iterator stateIter = states.begin(); stateIter != states.end(); stateIter++) {
//		stream << "_x"
//		std::list<std::string> origStates = _analyzer.getOrigState(stateIter->first);
//		size_t origIndex = 0;
//		for (std::list<std::string>::iterator origIter = origStates.begin(); origIter != origStates.end(); origIter++) {
//
//		}
//	}
}

void FSMToPromela::writeTypeDefs(std::ostream& stream) {
	stream << "/* typedefs */" << std::endl;
	PromelaCodeAnalyzer::PromelaTypedef typeDefs = _analyzer.getTypes();
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
//		if (currDef.name.compare("_x_t") == 0) {
//			stream << "typedef platform_t {" << std::endl;
//			if (_analyzer.usesInPredicate()) {
//				stream << "  bool states[" << _analyzer.getOrigStates().size() << "];" << std::endl;
//			}
//			stream << "};" << std::endl;
//
//			continue;
//		}
		stream << "typedef " << currDef.name << " {" << std::endl;
		if (currDef.name.compare("_event_t") == 0 && currDef.types.find("name") == currDef.types.end()) { // special treatment for _event
			stream << "  int name;" << std::endl;
		}
		for (std::map<std::string, PromelaCodeAnalyzer::PromelaTypedef>::iterator tIter = currDef.types.begin(); tIter != currDef.types.end(); tIter++) {
			if (currDef.name.compare("_x_t") == 0 && tIter->first.compare("states") == 0) {
				stream << "  bool states[" << _analyzer.getOrigStates().size() << "];" << std::endl;
				continue;
			}
			if (tIter->second.types.size() == 0) {
				stream << "  int " << tIter->first << ";" << std::endl; // not further nested
			} else {
				stream << "  " << tIter->second.name << " " << tIter->first << ";" << std::endl;
			}
		}
		stream << "};" << std::endl << std::endl;
	}

	stream << "/* typedef instances */" << std::endl;
	PromelaCodeAnalyzer::PromelaTypedef allTypes = _analyzer.getTypes();
	std::map<std::string, PromelaCodeAnalyzer::PromelaTypedef>::iterator typeIter = allTypes.types.begin();
	while(typeIter != allTypes.types.end()) {
		stream << typeIter->second.name << " " << typeIter->first << ";" << std::endl;
		typeIter++;
	}

}

Arabica::XPath::NodeSet<std::string> FSMToPromela::getTransientContent(const Arabica::DOM::Element<std::string>& state, const std::string& source) {
	Arabica::XPath::NodeSet<std::string> content;
	Arabica::DOM::Element<std::string> currState = state;
	FlatStateIdentifier prevFlatId(source);
	for (;;) {
		if (_analyzer.usesInPredicate()) {
			// insert state assignments into executable content

			std::stringstream stateSetPromela;
			stateSetPromela << "#promela-inline " << std::endl;
			FlatStateIdentifier currFlatId(ATTR(currState, "id"));
			stateSetPromela << "  /* from " << prevFlatId.getFlatActive() << " to " << currFlatId.getFlatActive() << " */" << std::endl;

			// add all that are missing from prevFlatId
			std::map<std::string, int> allOrigStates = _analyzer.getOrigStates();
			for (std::map<std::string, int>::iterator allOrigIter = allOrigStates.begin(); allOrigIter != allOrigStates.end(); allOrigIter++) {
				if (std::find(currFlatId.getActive().begin(), currFlatId.getActive().end(), allOrigIter->first) != currFlatId.getActive().end() &&
				        std::find(prevFlatId.getActive().begin(), prevFlatId.getActive().end(), allOrigIter->first) == prevFlatId.getActive().end()) {
					// active now but not previously
					stateSetPromela << "  _x.states[" << _analyzer.macroForLiteral(allOrigIter->first) << "] = true; " << std::endl;
				} else if (std::find(currFlatId.getActive().begin(), currFlatId.getActive().end(), allOrigIter->first) == currFlatId.getActive().end() &&
				           std::find(prevFlatId.getActive().begin(), prevFlatId.getActive().end(), allOrigIter->first) != prevFlatId.getActive().end()) {
					// previously active but not now
					stateSetPromela << "  _x.states[" << _analyzer.macroForLiteral(allOrigIter->first) << "] = false; " << std::endl;
				}
			}
			Comment<std::string> comment = _document.createComment(stateSetPromela.str());
			_document.importNode(comment, true);
			currState.insertBefore(comment, currState.getFirstChild());
			prevFlatId = currFlatId;
		}

		content.push_back(filterChildType(Node_base::COMMENT_NODE, currState));
		if (_analyzer.usesInPredicate()) assert(content.size() > 0);

		if (!HAS_ATTR(currState, "transient") || !DOMUtils::attributeIsTrue(ATTR(currState, "transient"))) {
			// breaking here causes final state assignment to be written
			break;
		}

		content.push_back(filterChildElements(_nsInfo.xmlNSPrefix + "invoke", currState));
		content.push_back(filterChildElements(_nsInfo.xmlNSPrefix + "onentry", currState));
		content.push_back(filterChildElements(_nsInfo.xmlNSPrefix + "onexit", currState));

		NodeSet<std::string> transitions = filterChildElements(_nsInfo.xmlNSPrefix + "transition", currState);
		currState = _states[ATTR_CAST(transitions[0], "target")];
	}
	return content;
}

Node<std::string> FSMToPromela::getUltimateTarget(const Arabica::DOM::Element<std::string>& transition) {
	if (!HAS_ATTR(transition, "target")) {
		return transition.getParentNode();
	}

	Arabica::DOM::Element<std::string> currState = _states[ATTR_CAST(transition, "target")];

	for (;;) {
		if (!HAS_ATTR(currState, "transient") || !DOMUtils::attributeIsTrue(ATTR(currState, "transient")))
			return currState;
		NodeSet<std::string> transitions = filterChildElements(_nsInfo.xmlNSPrefix + "transition", currState);
		currState = _states[ATTR_CAST(transitions[0], "target")];
	}
}

void FSMToPromela::writeInlineComment(std::ostream& stream, const Arabica::DOM::Node<std::string>& node) {
	if (node.getNodeType() != Node_base::COMMENT_NODE)
		return;

	std::string comment = node.getNodeValue();
	boost::trim(comment);
	if (!boost::starts_with(comment, "#promela-inline"))
		return;

	std::stringstream ssLine(comment);
	std::string line;
	std::getline(ssLine, line); // consume first line
	while(std::getline(ssLine, line)) {
		if (line.length() == 0)
			continue;
		stream << line;
	}
}

void FSMToPromela::writeExecutableContent(std::ostream& stream, const Arabica::DOM::Node<std::string>& node, int indent) {

//	std::cout << std::endl << node << std::endl;
	if (!node)
		return;

	std::string padding;
	for (int i = 0; i < indent; i++) {
		padding += "  ";
	}

//	std::cerr << node << std::endl;

	if (node.getNodeType() == Node_base::COMMENT_NODE) {
		// we cannot have labels in an atomic block, just process inline promela
		std::string comment = node.getNodeValue();
		boost::trim(comment);
		std::stringstream inlinePromela;
		if (!boost::starts_with(comment, "#promela-inline"))
			return;
		std::stringstream ssLine(comment);
		std::string line;
		std::getline(ssLine, line); // consume first line
		while(std::getline(ssLine, line)) {
			if (line.length() == 0)
				continue;
			inlinePromela << line << std::endl;
		}
		stream << padding << "skip;" << std::endl;
		stream << beautifyIndentation(inlinePromela.str(), indent) << std::endl;
	}

	if (node.getNodeType() != Node_base::ELEMENT_NODE)
		return;

	Arabica::DOM::Element<std::string> nodeElem = Arabica::DOM::Element<std::string>(node);

	if (false) {
//	} else if(TAGNAME(nodeElem) == "state") {
//		if (HAS_ATTR(nodeElem, "transient") && DOMUtils::attributeIsTrue(ATTR(nodeElem, "transient"))) {
//			Arabica::XPath::NodeSet<std::string> execContent = getTransientContent(nodeElem);
//			for (int i = 0; i < execContent.size(); i++) {
//				writeExecutableContent(stream, execContent[i], indent);
//			}
//		}
	} else if(TAGNAME(nodeElem) == "transition") {
		stream << "t" << _transitions[nodeElem] << ":";

		int number = _transitions[nodeElem];
		int digits = 0;
		do {
			number /= 10;
			digits++;
		} while (number != 0);

		INDENT_MIN(stream, 2 + digits, MIN_COMMENT_PADDING);

		Node<std::string> source = node.getParentNode();
		stream << " /* from state " << ATTR_CAST(source, "id") << " */" << std::endl;

		// gather all executable content
		NodeSet<std::string> execContent = getTransientContent(_states[ATTR(nodeElem, "target")], ATTR_CAST(source, "id"));

		// check for special promela labels
		if (HAS_ATTR(nodeElem, "target")) {
			PromelaInlines promInls = getInlinePromela(execContent, true);

			if (promInls.acceptLabels > 0)
				stream << padding << "acceptLabelT" << _transitions[nodeElem] << ":" << std::endl;
			if (promInls.endLabels > 0)
				stream << padding << "endLabelT" << _transitions[nodeElem] << ":" << std::endl;
			if (promInls.progressLabels > 0)
				stream << padding << "progressLabelT" << _transitions[nodeElem] << ":" << std::endl;
		}

		stream << padding << "atomic {" << std::endl;
//		writeExecutableContent(stream, _states[ATTR(nodeElem, "target")], indent+1);
		for (int i = 0; i < execContent.size(); i++) {
			writeExecutableContent(stream, execContent[i], indent+1);
		}
		stream << padding << "  skip;" << std::endl;

		Node<std::string> newState = getUltimateTarget(nodeElem);
		for (int i = 0; i < _globalStates.size(); i++) {
			if (newState != _globalStates[i])
				continue;

			std::string stateId = ATTR_CAST(_globalStates[i], "id");

			stream << padding << "  s = s" << i << ";";

			int number = i;
			int digits = 0;
			do {
				number /= 10;
				digits++;
			} while (number != 0);

			INDENT_MIN(stream, 10 + digits, MIN_COMMENT_PADDING);

			stream << " /* to state " << stateId << " */" << std::endl;

//			if (_analyzer.usesInPredicate()) {
//				FlatStateIdentifier flatId(stateId);
//				std::map<std::string, int> allOrigStates = _analyzer.getOrigStates();
//				for (std::map<std::string, int>::iterator allOrigIter = allOrigStates.begin(); allOrigIter != allOrigStates.end(); allOrigIter++) {
//					stream << padding << "  _x.states[" << _analyzer.macroForLiteral(allOrigIter->first) << "] = ";
//					if (std::find(flatId.getActive().begin(), flatId.getActive().end(), allOrigIter->first) != flatId.getActive().end()) {
//						stream << "true;" << std::endl;
//					} else {
//						stream << "false;" << std::endl;
//					}
//				}
//			}

		}

		stream << padding << "}" << std::endl;
		if (isFinal(Element<std::string>(newState))) {
			stream << padding << "goto terminate;";
			INDENT_MIN(stream, padding.length() + 14, MIN_COMMENT_PADDING);
			stream << "/* final state */" << std::endl;
		} else if (!HAS_ATTR_CAST(node, "event")) {
			stream << padding << "goto nextTransition;";
			INDENT_MIN(stream, padding.length() + 19, MIN_COMMENT_PADDING);
			stream << "/* spontaneous transition, check for more transitions */" << std::endl;
		} else {
			stream << padding << "eventLess = true;" << std::endl;
			stream << padding << "goto nextTransition;";
			INDENT_MIN(stream, padding.length() + 21, MIN_COMMENT_PADDING);
			stream << "/* ordinary transition, check for spontaneous transitions */" << std::endl;
		}

	} else if(TAGNAME(nodeElem) == "onentry" || TAGNAME(nodeElem) == "onexit") {
		Arabica::DOM::Node<std::string> child = node.getFirstChild();
		while(child) {
//			std::cerr << node << std::endl;
			if (child.getNodeType() == Node_base::TEXT_NODE) {
				if (boost::trim_copy(child.getNodeValue()).length() > 0)
					stream << beautifyIndentation(_analyzer.replaceLiterals(child.getNodeValue()), indent) << std::endl;
			}
			if (child.getNodeType() == Node_base::ELEMENT_NODE) {
				writeExecutableContent(stream, child, indent);
			}
			child = child.getNextSibling();
		}

	} else if(TAGNAME(nodeElem) == "script") {
		NodeSet<std::string> scriptText = filterChildType(Node_base::TEXT_NODE, node, true);
		for (int i = 0; i < scriptText.size(); i++) {
			stream << _analyzer.replaceLiterals(beautifyIndentation(scriptText[i].getNodeValue(), indent)) << std::endl;
		}

	} else if(TAGNAME(nodeElem) == "log") {
		std::string label = (HAS_ATTR(nodeElem, "label") ? ATTR(nodeElem, "label") : "");
		std::string expr = (HAS_ATTR(nodeElem, "expr") ? ATTR(nodeElem, "expr") : "");
		std::string trimmedExpr = boost::trim_copy(expr);
		bool isStringLiteral = (boost::starts_with(trimmedExpr, "\"") || boost::starts_with(trimmedExpr, "'"));

		std::string formatString;
		std::string varString;
		std::string seperator;

		if (label.size() > 0) {
			formatString += label + ": ";
		}

		if (isStringLiteral) {
			formatString += expr;
		} else {
			formatString += "%d";
			varString += seperator + expr;
		}

		if (varString.length() > 0) {
			stream << padding << "printf(\"" + formatString + "\", " + varString + ");" << std::endl;
		} else {
			stream << padding << "printf(\"" + formatString + "\");" << std::endl;
		}

	} else if(TAGNAME(nodeElem) == "foreach") {
		stream << padding << "for (" << (HAS_ATTR(nodeElem, "index") ? ATTR(nodeElem, "index") : "_index") << " in " << ATTR(nodeElem, "array") << ") {" << std::endl;
		if (HAS_ATTR(nodeElem, "item")) {
			stream << padding << "  " << ATTR(nodeElem, "item") << " = " << ATTR(nodeElem, "array") << "[" << (HAS_ATTR(nodeElem, "index") ? ATTR(nodeElem, "index") : "_index") << "];" << std::endl;
		}
		Arabica::DOM::Node<std::string> child = node.getFirstChild();
		while(child) {
			writeExecutableContent(stream, child, indent + 1);
			child = child.getNextSibling();
		}
		if (HAS_ATTR(nodeElem, "index"))
			stream << padding << "  " << ATTR(nodeElem, "index") << "++;" << std::endl;
		stream << padding << "}" << std::endl;

	} else if(TAGNAME(nodeElem) == "if") {
		NodeSet<std::string> condChain;
		condChain.push_back(node);
		condChain.push_back(filterChildElements(_nsInfo.xmlNSPrefix + "elseif", node));
		condChain.push_back(filterChildElements(_nsInfo.xmlNSPrefix + "else", node));

		writeIfBlock(stream, condChain, indent);

	} else if(TAGNAME(nodeElem) == "assign") {
		if (HAS_ATTR(nodeElem, "location")) {
			stream << padding << ATTR(nodeElem, "location") << " = ";
		}
		if (HAS_ATTR(nodeElem, "expr")) {
			stream << _analyzer.replaceLiterals(ATTR(nodeElem, "expr")) << ";" << std::endl;
		} else {
			NodeSet<std::string> assignTexts = filterChildType(Node_base::TEXT_NODE, nodeElem, true);
			if (assignTexts.size() > 0) {
				stream << _analyzer.replaceLiterals(boost::trim_copy(assignTexts[0].getNodeValue())) << ";" << std::endl;
			}
		}
	} else if(TAGNAME(nodeElem) == "send" || TAGNAME(nodeElem) == "raise") {
		std::string targetQueue;
		if (TAGNAME(nodeElem) == "raise") {
			targetQueue = "iQ!";
		} else if (!HAS_ATTR(nodeElem, "target")) {
			targetQueue = "tmpQ!";
		} else if (ATTR(nodeElem, "target").compare("#_internal") == 0) {
			targetQueue = "iQ!";
		}
		if (targetQueue.length() > 0) {
			// this is for our external queue
			std::string event;

			if (HAS_ATTR(nodeElem, "event")) {
				event = _analyzer.macroForLiteral(ATTR(nodeElem, "event"));
			} else if (HAS_ATTR(nodeElem, "eventexpr")) {
				event = ATTR(nodeElem, "eventexpr");
			}
			if (_analyzer.usesComplexEventStruct()) {
				stream << padding << "{" << std::endl;
				stream << padding << "  _event_t tmpEvent;" << std::endl;
				stream << padding << "  tmpEvent.name = " << event << ";" << std::endl;

				if (HAS_ATTR(nodeElem, "idlocation")) {
					stream << padding << "  /* idlocation */" << std::endl;
					stream << padding << "  _lastSendId = _lastSendId + 1;" << std::endl;
					stream << padding << "  " << ATTR(nodeElem, "idlocation") << " = _lastSendId;" << std::endl;
					stream << padding << "  tmpEvent.sendid = _lastSendId;" << std::endl;
					stream << padding << "  if" << std::endl;
					stream << padding << "  :: _lastSendId == 2147483647 -> _lastSendId = 0;" << std::endl;
					stream << padding << "  :: timeout -> skip;" << std::endl;
					stream << padding << "  fi;" << std::endl;
				} else if (HAS_ATTR(nodeElem, "id")) {
					stream << padding << "  tmpEvent.sendid = " << _analyzer.macroForLiteral(ATTR(nodeElem, "id")) << ";" << std::endl;
				}

				if (_analyzer.usesEventField("origintype") && targetQueue.compare("iQ!") != 0) {
					stream << padding << "  tmpEvent.origintype = " << _analyzer.macroForLiteral("http://www.w3.org/TR/scxml/#SCXMLEventProcessor") << ";" << std::endl;
				}

				if (_analyzer.usesEventField("type")) {
					std::string eventType = (targetQueue.compare("iQ!") == 0 ? _analyzer.macroForLiteral("internal") : _analyzer.macroForLiteral("external"));
					stream << padding << "  tmpEvent.type = " << eventType << ";" << std::endl;
				}

				NodeSet<std::string> sendParams = filterChildElements(_nsInfo.xmlNSPrefix + "param", nodeElem);
				NodeSet<std::string> sendContents = filterChildElements(_nsInfo.xmlNSPrefix + "content", nodeElem);
				std::string sendNameList = ATTR(nodeElem, "namelist");
				if (sendParams.size() > 0) {
					for (int i = 0; i < sendParams.size(); i++) {
						Element<std::string> paramElem = Element<std::string>(sendParams[i]);
						stream << padding << "  tmpEvent.data." << ATTR(paramElem, "name") << " = " << ATTR(paramElem, "expr")  << ";" << std::endl;
					}
				}
				if (sendNameList.size() > 0) {
					std::list<std::string> nameListIds = tokenizeIdRefs(sendNameList);
					std::list<std::string>::iterator nameIter = nameListIds.begin();
					while(nameIter != nameListIds.end()) {
						stream << padding << "  tmpEvent.data." << *nameIter << " = " << *nameIter << ";" << std::endl;
						nameIter++;
					}
				}

				if (sendParams.size() == 0 && sendNameList.size() == 0 && sendContents.size() > 0) {
					Element<std::string> contentElem = Element<std::string>(sendContents[0]);
					if (contentElem.hasChildNodes() && contentElem.getFirstChild().getNodeType() == Node_base::TEXT_NODE) {
						stream << padding << "  tmpEvent.data = " << spaceNormalize(contentElem.getFirstChild().getNodeValue()) << ";" << std::endl;
					} else if (HAS_ATTR(contentElem, "expr")) {
						stream << padding << "  tmpEvent.data = " << _analyzer.replaceLiterals(ATTR(contentElem, "expr")) << ";" << std::endl;
					}
				}
				stream << padding << "  " << targetQueue << "tmpEvent;" << std::endl;
				stream << padding << "}" << std::endl;
			} else {
				stream << padding << targetQueue << event << ";" << std::endl;
			}
		}
	} else if(TAGNAME(nodeElem) == "invoke") {
		_invokers[ATTR(nodeElem, "invokeid")].writeStartEventSources(stream, indent);
	} else if(TAGNAME(nodeElem) == "uninvoke") {
		stream << padding << ATTR(nodeElem, "invokeid") << "EventSourceDone" << "= 1;" << std::endl;
	} else {

		std::cerr << "'" << TAGNAME(nodeElem) << "'" << std::endl << nodeElem << std::endl;
		assert(false);
	}

}

PromelaInlines FSMToPromela::getInlinePromela(const std::string& content) {
	PromelaInlines prom;

	std::stringstream ssLine(content);
	std::string line;

	bool isInPromelaCode = false;
	bool isInPromelaEventSource = false;
	PromelaInline promInl;

	while(std::getline(ssLine, line)) {
		std::string trimLine = boost::trim_copy(line);
		if (trimLine.length() == 0)
			continue;
		if (boost::starts_with(trimLine, "#promela")) {
			if (isInPromelaCode || isInPromelaEventSource) {
				prom.inlines.push_back(promInl);
				isInPromelaCode = false;
				isInPromelaEventSource = false;
			}
			promInl = PromelaInline();
		}

		if (false) {
		} else if (boost::starts_with(trimLine, "#promela-progress")) {
			prom.progressLabels++;
			promInl.type = PromelaInline::PROMELA_PROGRESS_LABEL;
			promInl.content = line;
			prom.inlines.push_back(promInl);
		} else if (boost::starts_with(trimLine, "#promela-accept")) {
			prom.acceptLabels++;
			promInl.type = PromelaInline::PROMELA_ACCEPT_LABEL;
			promInl.content = line;
			prom.inlines.push_back(promInl);
		} else if (boost::starts_with(trimLine, "#promela-end")) {
			prom.endLabels++;
			promInl.type = PromelaInline::PROMELA_END_LABEL;
			promInl.content = line;
			prom.inlines.push_back(promInl);
		} else if (boost::starts_with(trimLine, "#promela-inline")) {
			prom.codes++;
			isInPromelaCode = true;
			promInl.type = PromelaInline::PROMELA_CODE;
		} else if (boost::starts_with(trimLine, "#promela-event-source-custom")) {
			prom.customEventSources++;
			isInPromelaCode = true;
			promInl.type = PromelaInline::PROMELA_EVENT_SOURCE_CUSTOM;
		} else if (boost::starts_with(trimLine, "#promela-event-source")) {
			prom.eventSources++;
			isInPromelaEventSource = true;
			promInl.type = PromelaInline::PROMELA_EVENT_SOURCE;
		} else if (isInPromelaCode) {
			promInl.content += line;
			promInl.content += "\n";
		} else if (isInPromelaEventSource) {
			std::list<std::string> seq;
			std::stringstream ssToken(trimLine);
			std::string token;
			while(std::getline(ssToken, token, ' ')) {
				if (token.length() == 0)
					continue;
				seq.push_back(token);
			}
			promInl.sequences.push_back(seq);
		}
	}
	// inline code ends with comment
	if (isInPromelaCode || isInPromelaEventSource) {
		prom.inlines.push_back(promInl);
	}

	return prom;
}

PromelaInlines FSMToPromela::getInlinePromela(const Arabica::DOM::Node<std::string>& node) {
	if (node.getNodeType() != Node_base::COMMENT_NODE)
		return getInlinePromela(std::string());
	return getInlinePromela(node.getNodeValue());
}

PromelaInlines FSMToPromela::getInlinePromela(const Arabica::XPath::NodeSet<std::string>& elements, bool recurse) {
	PromelaInlines allPromInls;

	Arabica::XPath::NodeSet<std::string> comments = filterChildType(Node_base::COMMENT_NODE, elements, recurse);
	for (int i = 0; i < comments.size(); i++) {
		allPromInls.merge(getInlinePromela(comments[i]));
	}
	return allPromInls;
}

void FSMToPromela::writeIfBlock(std::ostream& stream, const Arabica::XPath::NodeSet<std::string>& condChain, int indent) {
	if (condChain.size() == 0)
		return;

	std::string padding;
	for (int i = 0; i < indent; i++) {
		padding += "  ";
	}

	bool noNext = condChain.size() == 1;
	bool nextIsElse = false;
	if (condChain.size() > 1) {
		if (TAGNAME_CAST(condChain[1]) == "else") {
			nextIsElse = true;
		}
	}

	Element<std::string> ifNode = Element<std::string>(condChain[0]);

	stream << padding << "if" << std::endl;
	// we need to nest the elseifs to resolve promela if semantics
	stream << padding << ":: (" << _analyzer.replaceLiterals(ATTR(ifNode, "cond")) << ") -> {" << std::endl;

	Arabica::DOM::Node<std::string> child;
	if (TAGNAME(ifNode) == "if") {
		child = ifNode.getFirstChild();
	} else {
		child = ifNode.getNextSibling();
	}
	while(child) {
		if (child.getNodeType() == Node_base::ELEMENT_NODE) {
			Arabica::DOM::Element<std::string> childElem = Arabica::DOM::Element<std::string>(child);
			if (TAGNAME(childElem) == "elseif" || TAGNAME_CAST(childElem) == "else")
				break;
			writeExecutableContent(stream, childElem, indent + 1);
		}
		child = child.getNextSibling();
	}
	stream << padding << "}" << std::endl;
	stream << padding << ":: else -> ";

	if (nextIsElse) {
		child = condChain[1].getNextSibling();
		stream << "{" << std::endl;
		while(child) {
			if (child.getNodeType() == Node_base::ELEMENT_NODE) {
				writeExecutableContent(stream, child, indent + 1);
			}
			child = child.getNextSibling();
		}
		stream << padding << "}" << std::endl;

	} else if (noNext) {
		stream << "skip;" << std::endl;
	} else {
		stream << "{" << std::endl;

		Arabica::XPath::NodeSet<std::string> cdrCondChain;
		for (int i = 1; i < condChain.size(); i++) {
			cdrCondChain.push_back(condChain[i]);
		}
		writeIfBlock(stream, cdrCondChain, indent + 1);
		stream << padding << "}" << std::endl;

	}

	stream << padding << "fi;" << std::endl;

}

std::string FSMToPromela::beautifyIndentation(const std::string& code, int indent) {

	std::string padding;
	for (int i = 0; i < indent; i++) {
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

void FSMToPromela::writeStrings(std::ostream& stream) {
	stream << "/* string literals */" << std::endl;
	std::set<std::string> literals = _analyzer.getLiterals();
	std::map<std::string, int> events = _analyzer.getEvents();
	std::map<std::string, int> origStates = _analyzer.getOrigStates();

	for (std::set<std::string>::const_iterator litIter = literals.begin(); litIter != literals.end(); litIter++) {
		if (events.find(*litIter) == events.end() && (origStates.find(*litIter) == origStates.end() || !_analyzer.usesInPredicate()))
			stream << "#define " << _analyzer.macroForLiteral(*litIter) << " " << _analyzer.indexForLiteral(*litIter) << " /* " << *litIter << " */" << std::endl;
	}
}

void FSMToPromela::writeDeclarations(std::ostream& stream) {

	// get all data elements
	NodeSet<std::string> datas = _xpath.evaluate("//" + _nsInfo.xpathPrefix + "data", _scxml).asNodeSet();
//	NodeSet<std::string> dataText = filterChildType(Node_base::TEXT_NODE, datas, true);

	// write their text content
	stream << "/* datamodel variables */" << std::endl;
	std::set<std::string> processedIdentifiers;
	for (int i = 0; i < datas.size(); i++) {

		Node<std::string> data = datas[i];
		if (isInEmbeddedDocument(data))
			continue;

		std::string identifier = (HAS_ATTR_CAST(data, "id") ? ATTR_CAST(data, "id") : "");
		std::string expression = (HAS_ATTR_CAST(data, "expr") ? ATTR_CAST(data, "expr") : "");
		std::string type = boost::trim_copy(HAS_ATTR_CAST(data, "type") ? ATTR_CAST(data, "type") : "");

		if (processedIdentifiers.find(identifier) != processedIdentifiers.end())
			continue;
		processedIdentifiers.insert(identifier);

		if (boost::starts_with(type, "string")) {
			type = "int" + type.substr(6, type.length() - 6);
		}
		std::string arrSize;

		NodeSet<std::string> dataText = filterChildType(Node_base::TEXT_NODE, data, true);
		std::string value;
		if (dataText.size() > 0) {
			value = dataText[0].getNodeValue();
			boost::trim(value);
		}

		if (identifier.length() > 0) {

			size_t bracketPos = type.find("[");
			if (bracketPos != std::string::npos) {
				arrSize = type.substr(bracketPos, type.length() - bracketPos);
				type = type.substr(0, bracketPos);
			}
			std::string decl = type + " " + identifier + arrSize;

			if (arrSize.length() > 0) {
				stream << decl << ";" << std::endl;
				_varInitializers.push_back(value);
			} else {
				stream << decl;
				if (expression.length() > 0) {
					// id and expr given
					stream << " = " << _analyzer.replaceLiterals(boost::trim_copy(expression)) << ";" << std::endl;
				} else if (value.length() > 0) {
					// id and text content given
					stream << " = " << _analyzer.replaceLiterals(value) << ";" << std::endl;
				} else {
					// only id given
					stream << ";" << std::endl;
				}
			}
		} else if (value.length() > 0) {
			// no id but text content given
			stream << beautifyIndentation(value) << std::endl;
		}
	}

	stream << std::endl;
	stream << "/* global variables */" << std::endl;

	if (_analyzer.usesComplexEventStruct()) {
		// event is defined with the typedefs
		stream << "unsigned s : " << BIT_WIDTH(_globalStates.size() + 1) << ";            /* current state */" << std::endl;
		stream << "chan iQ   = [10] of {_event_t}  /* internal queue */" << std::endl;
		stream << "chan eQ   = [10] of {_event_t}  /* external queue */" << std::endl;
		stream << "chan tmpQ = [10] of {_event_t}  /* temporary queue for external events in transitions */" << std::endl;
		stream << "_event_t tmpQItem;" << std::endl;
	} else {
		stream << "unsigned _event : " << BIT_WIDTH(_analyzer.getEvents().size() + 1) << ";                /* current event */" << std::endl;
		stream << "unsigned s : " << BIT_WIDTH(_globalStates.size() + 1) << ";            /* current state */" << std::endl;
		stream << "chan iQ   = [10] of {int}  /* internal queue */" << std::endl;
		stream << "chan eQ   = [10] of {int}  /* external queue */" << std::endl;
		stream << "chan tmpQ = [10] of {int}  /* temporary queue for external events in transitions */" << std::endl;
		stream << "unsigned tmpQItem : " << BIT_WIDTH(_analyzer.getEvents().size() + 1) << ";" << std::endl;
	}
	stream << "bool eventLess = true;       /* whether to process event-less only n this step */" << std::endl;
	stream << "hidden int _index;                  /* helper for indexless foreach loops */" << std::endl;

	if (_analyzer.usesEventField("sendid")) {
		stream << "hidden int _lastSendId = 0;         /* sequential counter for send ids */";
	}

//	if (_analyzer.usesPlatformVars()) {
//		stream << "_x_t _x;" << std::endl;
//	}

	stream << std::endl;
	stream << "/* event sources */" << std::endl;

	if (_globalEventSource) {
		_globalEventSource.writeDeclarations(stream);
	}

	std::map<std::string, PromelaEventSource>::iterator invIter = _invokers.begin();
	while(invIter != _invokers.end()) {
		invIter->second.writeDeclarations(stream);
		invIter++;
	}

}

void FSMToPromela::writeEventSources(std::ostream& stream) {
	std::list<PromelaInline>::iterator inlineIter;

	if (_globalEventSource) {
		_globalEventSource.writeEventSource(stream);
	}

	std::map<std::string, PromelaEventSource>::iterator invIter = _invokers.begin();
	while(invIter != _invokers.end()) {
		invIter->second.writeEventSource(stream);
		invIter++;
	}
}

void FSMToPromela::writeFSM(std::ostream& stream) {
	NodeSet<std::string> transitions;

	stream << "proctype step() {" << std::endl;
	// write initial transition
	transitions = filterChildElements(_nsInfo.xmlNSPrefix + "transition", _startState);
	assert(transitions.size() == 1);
	stream << "  /* transition's executable content */" << std::endl;
	writeExecutableContent(stream, transitions[0], 1);

	for (int i = 0; i < _globalStates.size(); i++) {
		if (_globalStates[i] == _startState)
			continue;
		NodeSet<std::string> transitions = filterChildElements(_nsInfo.xmlNSPrefix + "transition", _globalStates[i]);
		for (int j = 0; j < transitions.size(); j++) {
			writeExecutableContent(stream, transitions[j], 1);
		}
	}

	stream << std::endl;
	stream << "nextStep:" << std::endl;
	stream << "  /* push send events to external queue */" << std::endl;
	stream << "  if" << std::endl;
	stream << "  :: len(tmpQ) != 0 -> { tmpQ?_event; eQ!_event }" << std::endl;
	stream << "  :: else -> skip;" << std::endl;
	stream << "  fi;" << std::endl << std::endl;

	stream << "  /* pop an event */" << std::endl;
	stream << "  if" << std::endl;
	stream << "  :: len(iQ) != 0 -> iQ ? _event   /* from internal queue */" << std::endl;
	stream << "  :: else -> eQ ? _event           /* from external queue */" << std::endl;
	stream << "  fi;" << std::endl << std::endl;
	stream << "  /* event dispatching per state */" << std::endl;
	stream << "nextTransition:" << std::endl;
	stream << "  if" << std::endl;

	writeEventDispatching(stream);

	stream << "  :: else -> assert(false);   /* this is an error as we dispatched all valid states */" << std::endl;
	stream << "  fi;" << std::endl;
	stream << "terminate: skip;" << std::endl;

	// stop all event sources
	if (_globalEventSource)
		_globalEventSource.writeStopEventSources(stream, 1);

	std::map<std::string, PromelaEventSource>::iterator invIter = _invokers.begin();
	while(invIter != _invokers.end()) {
		invIter->second.writeStopEventSources(stream, 1);
		invIter++;
	}

	stream << "}" << std::endl;
}

void FSMToPromela::writeEventDispatching(std::ostream& stream) {
	for (int i = 0; i < _globalStates.size(); i++) {
		if (_globalStates[i] == _startState)
			continue;

		int number = i;
		int digits = 0;
		do {
			number /= 10;
			digits++;
		} while (number != 0);
		stream << "  :: (s == s" << i << ") -> {";

		INDENT_MIN(stream, 18 + digits, MIN_COMMENT_PADDING);

		stream << " /* from state " << ATTR_CAST(_globalStates[i], "id") << " */" << std::endl;

		NodeSet<std::string> transitions = filterChildElements(_nsInfo.xmlNSPrefix + "transition", _globalStates[i]);
		writeDispatchingBlock(stream, transitions, 2);
//		stream << "    goto nextStep;";
		stream << "  }" << std::endl;
	}
}

void FSMToPromela::writeDispatchingBlock(std::ostream& stream, const Arabica::XPath::NodeSet<std::string>& transChain, int indent) {
	std::string padding;
	for (int i = 0; i < indent; i++) {
		padding += "  ";
	}

	if (transChain.size() == 0) {
		stream << padding << "eventLess = false;" << std::endl;
		stream << padding << "goto nextStep;";
		INDENT_MIN(stream, padding.size() + 13, MIN_COMMENT_PADDING);
		stream << "/* no transition applicable */" << std::endl;
		return;
	}


	Element<std::string> currTrans = Element<std::string>(transChain[0]);
	std::stringstream tmpSS;

	tmpSS << padding << "if" << std::endl;
	size_t lineStart = tmpSS.tellp();

	if (HAS_ATTR(currTrans, "cond")) {
		tmpSS << padding << ":: ((";
	} else {
		tmpSS << padding << ":: (";
	}

	if (!HAS_ATTR(currTrans, "event")) {
		tmpSS << "eventLess";
	} else {
		std::string eventDescs = ATTR(currTrans, "event");

		std::list<std::string> eventNames = tokenizeIdRefs(eventDescs);
		std::set<std::string> eventPrefixes;
		std::list<std::string>::iterator eventNameIter = eventNames.begin();
		while(eventNameIter != eventNames.end()) {
			std::string eventDesc = *eventNameIter;
			if (boost::ends_with(eventDesc, "*"))
				eventDesc = eventDesc.substr(0, eventDesc.size() - 1);
			if (boost::ends_with(eventDesc, "."))
				eventDesc = eventDesc.substr(0, eventDesc.size() - 1);
			if (eventDesc.length() > 0) {
				std::set<std::string> tmp = _analyzer.getEventsWithPrefix(*eventNameIter);
				eventPrefixes.insert(tmp.begin(), tmp.end());
			}
			eventNameIter++;
		}

		if (eventPrefixes.size() > 0) {
			tmpSS << "!eventLess && ";
		} else {
			tmpSS << "!eventLess";
		}

		std::string seperator;
		std::set<std::string>::iterator eventIter = eventPrefixes.begin();
		while(eventIter != eventPrefixes.end()) {
			if (_analyzer.usesComplexEventStruct()) {
				tmpSS << seperator << "_event.name == " << _analyzer.macroForLiteral(*eventIter);
			} else {
				tmpSS << seperator << "_event == " << _analyzer.macroForLiteral(*eventIter);
			}
			seperator = " || ";
			eventIter++;
		}
	}

	tmpSS << ")";
	if (HAS_ATTR(currTrans, "cond")) {
		tmpSS << (HAS_ATTR(currTrans, "cond") ? " && " + _analyzer.replaceLiterals(ATTR(currTrans, "cond")) + ")": "");
	}
	tmpSS << " -> goto t" << _transitions[currTrans] << ";";
	size_t lineEnd = tmpSS.tellp();
	size_t lineLength = lineEnd - lineStart;

	for (int i = lineLength; i < MIN_COMMENT_PADDING; i++)
		tmpSS << " ";

	tmpSS << " /* transition to " << ATTR_CAST(getUltimateTarget(currTrans), "id") << " */" << std::endl;
	stream << tmpSS.str();

	stream << padding << ":: else {" << std::endl;

	Arabica::XPath::NodeSet<std::string> cdrTransChain;
	for (int i = 1; i < transChain.size(); i++) {
		cdrTransChain.push_back(transChain[i]);
	}
	writeDispatchingBlock(stream, cdrTransChain, indent + 1);

	stream << padding << "}" << std::endl;
	stream << padding << "fi;" << std::endl;
}


void FSMToPromela::writeMain(std::ostream& stream) {
	stream << std::endl;
	stream << "init {" << std::endl;
	if (_varInitializers.size() > 0) {
		std::list<std::string>::iterator initIter = _varInitializers.begin();
		while(initIter != _varInitializers.end()) {
			stream << beautifyIndentation(*initIter);
			initIter++;
		}
		stream << std::endl;
	}
	if (_globalEventSource)
		_globalEventSource.writeStartEventSources(stream, 1);
	stream << "  run step();" << std::endl;
	stream << "}" << std::endl;

}


void FSMToPromela::initNodes() {
	// get all states
	NodeSet<std::string> states = filterChildElements(_nsInfo.xmlNSPrefix + "state", _scxml);
	for (int i = 0; i < states.size(); i++) {
		if (InterpreterImpl::isInEmbeddedDocument(states[i]))
			continue;
		_states[ATTR_CAST(states[i], "id")] = Element<std::string>(states[i]);
		_analyzer.addState(ATTR_CAST(states[i], "id"));
		if (HAS_ATTR_CAST(states[i], "transient") && DOMUtils::attributeIsTrue(ATTR_CAST(states[i], "transient")))
			continue;
		_globalStates.push_back(states[i]);
	}
	_startState = _states[ATTR(_scxml, "initial")];

	// initialize event trie with all events that might occur
	NodeSet<std::string> internalEventNames;
	internalEventNames.push_back(_xpath.evaluate("//" + _nsInfo.xpathPrefix + "transition", _scxml).asNodeSet());
	internalEventNames.push_back(_xpath.evaluate("//" + _nsInfo.xpathPrefix + "raise", _scxml).asNodeSet());
	internalEventNames.push_back(_xpath.evaluate("//" + _nsInfo.xpathPrefix + "send", _scxml).asNodeSet());

	for (int i = 0; i < internalEventNames.size(); i++) {
		if (HAS_ATTR_CAST(internalEventNames[i], "event")) {
			std::string eventNames = ATTR_CAST(internalEventNames[i], "event");
			std::list<std::string> events = tokenizeIdRefs(eventNames);
			for (std::list<std::string>::iterator eventIter = events.begin();
			        eventIter != events.end(); eventIter++) {
				std::string eventName = *eventIter;
				if (boost::ends_with(eventName, "*"))
					eventName = eventName.substr(0, eventName.size() - 1);
				if (boost::ends_with(eventName, "."))
					eventName = eventName.substr(0, eventName.size() - 1);
				if (eventName.size() > 0)
					_analyzer.addEvent(eventName);
			}
		}
	}

	// do we need sendid / invokeid?
	{
		NodeSet<std::string> invokes = filterChildElements(_nsInfo.xmlNSPrefix + "invoke", _scxml, true);
		NodeSet<std::string> sends = filterChildElements(_nsInfo.xmlNSPrefix + "send", _scxml, true);

		for (int i = 0; i < invokes.size(); i++) {
			if (HAS_ATTR_CAST(invokes[i], "idlocation")) {
			}
		}

		for (int i = 0; i < sends.size(); i++) {
			if (HAS_ATTR_CAST(sends[i], "idlocation")) {
				_analyzer.addCode("_event.sendid");
			}
			if (HAS_ATTR_CAST(sends[i], "id")) {
				_analyzer.addLiteral(ATTR_CAST(sends[i], "id"));
				_analyzer.addCode("_event.sendid");
			}
		}

	}
	// external event names from comments
	NodeSet<std::string> promelaEventSourceComments;
	NodeSet<std::string> invokers = _xpath.evaluate("//" + _nsInfo.xpathPrefix + "invoke", _scxml).asNodeSet();
	promelaEventSourceComments.push_back(filterChildType(Node_base::COMMENT_NODE, invokers, false)); // comments in invoke elements
	promelaEventSourceComments.push_back(filterChildType(Node_base::COMMENT_NODE, _scxml, false)); // comments in scxml element

	for (int i = 0; i < promelaEventSourceComments.size(); i++) {
		PromelaInlines promInls = getInlinePromela(promelaEventSourceComments[i]);
		PromelaEventSource promES(promInls, promelaEventSourceComments[i].getParentNode());

		if (TAGNAME_CAST(promelaEventSourceComments[i].getParentNode()) == "scxml") {
			promES.type = PromelaEventSource::PROMELA_EVENT_SOURCE_GLOBAL;
			promES.analyzer = &_analyzer;
			promES.name = "global";
			_globalEventSource = promES;
		} else if (TAGNAME_CAST(promelaEventSourceComments[i].getParentNode()) == "invoke") {
			if (!HAS_ATTR_CAST(promelaEventSourceComments[i].getParentNode(), "invokeid")) {
				Element<std::string> invoker = Element<std::string>(promelaEventSourceComments[i].getParentNode());
				invoker.setAttribute("invokeid", "invoker" + toStr(_invokers.size()));
			}
			std::string invokeId = ATTR_CAST(promelaEventSourceComments[i].getParentNode(), "invokeid");
			promES.type = PromelaEventSource::PROMELA_EVENT_SOURCE_INVOKER;
			promES.analyzer = &_analyzer;
			promES.name = invokeId;
			_invokers[invokeId] = promES;
		}
	}

	// enumerate transitions
	NodeSet<std::string> transitions = filterChildElements(_nsInfo.xmlNSPrefix + "transition", _scxml, true);
	int index = 0;
	for (int i = 0; i < transitions.size(); i++) {
		_transitions[Element<std::string>(transitions[i])] = index++;
	}

	// add platform variables as string literals
	_analyzer.addLiteral("_sessionid");
	_analyzer.addLiteral("_name");

	if (HAS_ATTR(_scxml, "name")) {
		_analyzer.addLiteral(ATTR(_scxml, "name"), _analyzer.indexForLiteral("_sessionid"));
	}

	NodeSet<std::string> contents = filterChildElements(_nsInfo.xmlNSPrefix + "content", _scxml, true);
	for (int i = 0; i < contents.size(); i++) {
		Element<std::string> contentElem = Element<std::string>(contents[i]);
		if (contentElem.hasChildNodes() && contentElem.getFirstChild().getNodeType() == Node_base::TEXT_NODE) {
			_analyzer.addLiteral(spaceNormalize(contentElem.getFirstChild().getNodeValue()));
		}
	}


	// extract and analyze source code
	std::set<std::string> allCode;
	std::set<std::string> allStrings;
	{
		NodeSet<std::string> withCond;
		withCond.push_back(filterChildElements(_nsInfo.xmlNSPrefix + "transition", _scxml, true));
		withCond.push_back(filterChildElements(_nsInfo.xmlNSPrefix + "if", _scxml, true));
		withCond.push_back(filterChildElements(_nsInfo.xmlNSPrefix + "elseif", _scxml, true));
		for (int i = 0; i < withCond.size(); i++) {
			Element<std::string> elem = Element<std::string>(withCond[i]);
			if (HAS_ATTR(elem, "cond")) {
				std::string code = ATTR(elem, "cond");
				code = sanitizeCode(code);
				elem.setAttribute("cond", code);
				allCode.insert(code);
			}
		}
	}
	{
		NodeSet<std::string> withExpr;
		withExpr.push_back(filterChildElements(_nsInfo.xmlNSPrefix + "log", _scxml, true));
		withExpr.push_back(filterChildElements(_nsInfo.xmlNSPrefix + "data", _scxml, true));
		withExpr.push_back(filterChildElements(_nsInfo.xmlNSPrefix + "assign", _scxml, true));
		withExpr.push_back(filterChildElements(_nsInfo.xmlNSPrefix + "content", _scxml, true));
		withExpr.push_back(filterChildElements(_nsInfo.xmlNSPrefix + "param", _scxml, true));
		for (int i = 0; i < withExpr.size(); i++) {
			Element<std::string> elem = Element<std::string>(withExpr[i]);
			if (HAS_ATTR(elem, "expr")) {
				std::string code = ATTR(elem, "expr");
				code = sanitizeCode(code);
				elem.setAttribute("expr", code);
				allCode.insert(code);
			}
		}
	}
	{
		NodeSet<std::string> withLocation;
		withLocation.push_back(filterChildElements(_nsInfo.xmlNSPrefix + "assign", _scxml, true));
		for (int i = 0; i < withLocation.size(); i++) {
			Element<std::string> elem = Element<std::string>(withLocation[i]);
			if (HAS_ATTR(elem, "location")) {
				std::string code = ATTR(elem, "location");
				code = sanitizeCode(code);
				elem.setAttribute("location", code);
				allCode.insert(code);
			}
		}
	}
	{
		NodeSet<std::string> withText;
		withText.push_back(filterChildElements(_nsInfo.xmlNSPrefix + "script", _scxml, true));
		withText.push_back(filterChildElements(_nsInfo.xmlNSPrefix + "data", _scxml, true));
		for (int i = 0; i < withText.size(); i++) {
			NodeSet<std::string> texts = filterChildType(Node_base::TEXT_NODE, withText[i], true);
			for (int j = 0; j < texts.size(); j++) {
				if (texts[j].getNodeValue().size() > 0) {
					Text<std::string> elem = Text<std::string>(texts[j]);
					std::string code = elem.getNodeValue();
					code = sanitizeCode(code);
					elem.setNodeValue(code);
					allCode.insert(code);
				}
			}
		}
	}
	for (std::set<std::string>::const_iterator codeIter = allCode.begin(); codeIter != allCode.end(); codeIter++) {
		_analyzer.addCode(*codeIter);
	}

}

std::string FSMToPromela::sanitizeCode(const std::string& code) {
	std::string replaced = code;
	boost::replace_all(replaced, "\"", "'");
	boost::replace_all(replaced, "_sessionid", "_SESSIONID");
	boost::replace_all(replaced, "_name", "_NAME");
	return replaced;
}

void PromelaInline::dump() {
	std::list<std::list<std::string> >::iterator outerIter = sequences.begin();
	while(outerIter != sequences.end()) {
		std::list<std::string>::iterator innerIter = outerIter->begin();
		while(innerIter != outerIter->end()) {
			std::cout << *innerIter << " ";
			innerIter++;
		}
		std::cout << std::endl;
		outerIter++;
	}
}

void FSMToPromela::writeProgram(std::ostream& stream) {

	if (!HAS_ATTR(_scxml, "flat") || !DOMUtils::attributeIsTrue(ATTR(_scxml, "flat"))) {
		LOG(ERROR) << "Given SCXML document was not flattened";
		return;
	}

	if (!HAS_ATTR(_scxml, "datamodel") || ATTR(_scxml, "datamodel") != "promela") {
		LOG(ERROR) << "Can only convert SCXML documents with \"promela\" datamodel";
		return;
	}

	if (HAS_ATTR(_scxml, "binding") && ATTR(_scxml, "binding") != "early") {
		LOG(ERROR) << "Can only convert for early data bindings";
		return;
	}

//	std::cerr << _scxml << std::endl;

	initNodes();

	writeEvents(stream);
	stream << std::endl;
	writeStates(stream);
	stream << std::endl;
	if (_analyzer.usesInPredicate()) {
		writeStateMap(stream);
		stream << std::endl;
	}
	writeTypeDefs(stream);
	stream << std::endl;
	writeStrings(stream);
	stream << std::endl;
	writeDeclarations(stream);
	stream << std::endl;
	writeEventSources(stream);
	stream << std::endl;
	writeFSM(stream);
	stream << std::endl;
	writeMain(stream);
	stream << std::endl;

	// write ltl expression for success
	std::stringstream acceptingStates;
	std::string seperator;
	for (int i = 0; i < _globalStates.size(); i++) {
		FlatStateIdentifier flatId(ATTR_CAST(_globalStates[i], "id"));
		if (std::find(flatId.getActive().begin(), flatId.getActive().end(), "pass") != flatId.getActive().end()) {
			acceptingStates << seperator << "s == s" << i;
			seperator = " || ";
		}
	}
	if (acceptingStates.str().size() > 0) {
		stream << "ltl { eventually (" << acceptingStates.str() << ") }" << std::endl;
	}

//	if (_states.find("active:{pass}") != _states.end()) {
//		for (int i = 0; i < _globalStates.size(); i++) {
//			if (_states["active:{pass}"] != _globalStates[i])
//				continue;
//			stream << "ltl { eventually (s == s" << i << ") }";
//			break;
//		}
//	}
}

}