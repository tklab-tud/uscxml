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
#include "uscxml/transform/ChartToPromela.h"
#include "uscxml/transform/FlatStateIdentifier.h"
#include "uscxml/plugins/datamodel/promela/PromelaParser.h"
#include "uscxml/plugins/datamodel/promela/parser/promela.tab.hpp"

#include <DOM/io/Stream.hpp>
#include <iostream>
#include "uscxml/UUID.h"
#include <math.h>
#include <boost/algorithm/string.hpp>
#include <glog/logging.h>

#define MSG_QUEUE_LENGTH 5
#define MAX_MACRO_CHARS 64
#define MIN_COMMENT_PADDING 60
#define MAX(X,Y) ((X) > (Y) ? (X) : (Y))

#define ADAPT_SRC(code) _analyzer->adaptCode(code, _prefix)

#define BIT_WIDTH(number) (number > 1 ? (int)ceil(log((double)number) / log((double)2.0)) : 1)
#define LENGTH_FOR_NUMBER(input, output) \
{ \
	int number = input; \
	int output = 0; \
	do { \
		number /= 10; \
		output++; \
	} while (number != 0); \
}

#define INDENT_MIN(stream, start, cols) \
for (int indentIndex = start; indentIndex < cols; indentIndex++) \
	stream << " ";

#define DIFF_MAPS(base, compare, result) \
{ \
	histIter_t baseIter = base.begin(); \
	while(baseIter != base.end()) { \
		if (compare.find(baseIter->first) == compare.end()) { \
			result[baseIter->first] = baseIter->second; \
		} else { \
			histMemberIter_t baseMemberIter = baseIter->second.begin(); \
			while(baseMemberIter != baseIter->second.end()) { \
				if (compare.at(baseIter->first).find(*baseMemberIter) == compare.at(baseIter->first).end()) { \
					result[baseIter->first].insert(*baseMemberIter); \
				} \
				baseMemberIter++; \
			} \
		} \
		baseIter++; \
	} \
}

#define INTERSECT_MAPS(base, compare, result) \
{ \
	histIter_t baseIter = base.begin(); \
	while(baseIter != base.end()) { \
		if (compare.find(baseIter->first) != compare.end()) { \
			histMemberIter_t baseMemberIter = baseIter->second.begin(); \
			while(baseMemberIter != baseIter->second.end()) { \
				if (compare.at(baseIter->first).find(*baseMemberIter) != compare.at(baseIter->first).end()) { \
					result[baseIter->first].insert(*baseMemberIter); \
				} \
				baseMemberIter++; \
			} \
		} \
		baseIter++; \
	} \
}

#define PRETTY_PRINT_LIST(stream, var) \
{ \
	std::list<std::string>::const_iterator listIter = var.begin(); \
	std::string sep;\
	while(listIter != var.end()) { \
		stream << sep << *listIter; \
		sep = ", "; \
		listIter++; \
	} \
}


namespace uscxml {

using namespace Arabica::DOM;
using namespace Arabica::XPath;

Transformer ChartToPromela::transform(const Interpreter& other) {
	return boost::shared_ptr<TransformerImpl>(new ChartToPromela(other));
}

void ChartToPromela::writeTo(std::ostream& stream) {
	writeProgram(stream);
}

void PromelaEventSource::writeStart(std::ostream& stream, int indent) {
	std::string padding;
	for (int i = 0; i < indent; i++) {
		padding += "  ";
	}
	stream << padding << "run " << name << "EventSource() priority 10;" << std::endl;
}

void PromelaEventSource::writeStop(std::ostream& stream, int indent) {
	std::string padding;
	for (int i = 0; i < indent; i++) {
		padding += "  ";
	}

	stream << padding << name << "EventSourceDone = 1;" << std::endl;
}

void PromelaEventSource::writeDeclarations(std::ostream& stream, int indent) {
	std::string padding;
	for (int i = 0; i < indent; i++) {
		padding += "  ";
	}
	stream << "bool " << name << "EventSourceDone = 0;" << std::endl;
	
}

void PromelaEventSource::writeBody(std::ostream& stream) {

	
	stream << "proctype " << name << "EventSource() {" << std::endl;
	stream << "  " << name << "EventSourceDone = 0;" << std::endl;
	if (analyzer->usesComplexEventStruct()) {
		stream << "  _event_t tmpE;" << std::endl;
	}
	stream << "  " << name << "NewEvent:" << std::endl;
	stream << "  " << "if" << std::endl;
	stream << "  " << ":: " << name << "EventSourceDone -> goto " << name << "Done;" << std::endl;
	stream << "  " << ":: " << "len(eQ) >= " << externalQueueLength - longestSequence << " -> skip;" << std::endl;
	stream << "  " << ":: else { " << std::endl;

	Trie& trie = analyzer->getTrie();
	if (source.type == PromelaInline::PROMELA_EVENT_SOURCE_CUSTOM) {
		// custom event source
		std::string content = source.content;

		boost::replace_all(content, "#REDO#", name + "NewEvent");
		boost::replace_all(content, "#DONE#", name + "Done");

		std::list<TrieNode*> eventNames = trie.getChildsWithWords(trie.getNodeWithPrefix(""));
		std::list<TrieNode*>::iterator eventNameIter = eventNames.begin();
		while(eventNameIter != eventNames.end()) {
			boost::replace_all(content, "#" + (*eventNameIter)->value + "#", (*eventNameIter)->identifier);
			eventNameIter++;
		}

		stream << ChartToPromela::beautifyIndentation(content, 2) << std::endl;
	} else {
		// standard event source
		stream << "  " << "  if" << std::endl;
//		stream << "  " << "  :: 1 -> " << "goto " << sourceName << "NewEvent;" << std::endl;

		std::list<std::list<std::string> >::const_iterator seqIter = sequences.begin();
		while(seqIter != sequences.end()) {
			stream << "    " << ":: skip -> { ";
			std::list<std::string>::const_iterator evIter = seqIter->begin();
			while(evIter != seqIter->end()) {
				TrieNode* node = trie.getNodeWithPrefix(*evIter);
				if (!node) {
					std::cerr << "Event " << *evIter << " defined in event source but never used in transitions" << std::endl;
					evIter++;
					continue;
				}
				if (analyzer->usesComplexEventStruct()) {
					stream << "tmpE.name = " << analyzer->macroForLiteral(node->value) << "; eQ!tmpE; ";
				} else {
					stream << "eQ!" << analyzer->macroForLiteral(node->value) << "; ";
				}
				evIter++;
			}
			stream << "goto " << name << "NewEvent;";
			stream << " }" << std::endl;
			seqIter++;
		}

		stream << "  " << "  fi;" << std::endl;
	}

	stream << "  " << "}" << std::endl;
	stream << "  " << "fi;" << std::endl;
	stream << name << "Done:" << " skip;" << std::endl;
	stream << "}" << std::endl;

	
//	std::list<PromelaInline>::iterator sourceIter = eventSources.inlines.begin();
//	int i = 0;
//	while(sourceIter != eventSources.inlines.end()) {
//		if (sourceIter->type != PromelaInline::PROMELA_EVENT_SOURCE_CUSTOM && sourceIter->type != PromelaInline::PROMELA_EVENT_SOURCE) {
//			sourceIter++;
//			continue;
//		}
//
//		std::string sourceName = name + "_"+ toStr(i);
//
//		stream << "proctype " << sourceName << "EventSource() {" << std::endl;
//		stream << "  " << sourceName << "EventSourceDone = 0;" << std::endl;
//		stream << "  " << sourceName << "NewEvent:" << std::endl;
//		stream << "  " << "if" << std::endl;
//		stream << "  " << ":: " << sourceName << "EventSourceDone -> skip;" << std::endl;
//		stream << "  " << ":: else { " << std::endl;
//
//		Trie& trie = analyzer->getTrie();
//
//		if (sourceIter->type == PromelaInline::PROMELA_EVENT_SOURCE_CUSTOM) {
//			std::string content = sourceIter->content;
//
//			boost::replace_all(content, "#REDO#", sourceName + "NewEvent");
//			boost::replace_all(content, "#DONE#", sourceName + "Done");
//
//			std::list<TrieNode*> eventNames = trie.getChildsWithWords(trie.getNodeWithPrefix(""));
//			std::list<TrieNode*>::iterator eventNameIter = eventNames.begin();
//			while(eventNameIter != eventNames.end()) {
//				boost::replace_all(content, "#" + (*eventNameIter)->value + "#", (*eventNameIter)->identifier);
//				eventNameIter++;
//			}
//
//			stream << ChartToPromela::beautifyIndentation(content, 2) << std::endl;
//
//		} else {
//			stream << "  " << "  if" << std::endl;
////			stream << "  " << "  :: 1 -> " << "goto " << sourceName << "NewEvent;" << std::endl;
//
//			std::list<std::list<std::string> >::const_iterator seqIter = sourceIter->sequences.begin();
//			while(seqIter != sourceIter->sequences.end()) {
//				stream << "    " << ":: ";
//				std::list<std::string>::const_iterator evIter = seqIter->begin();
//				while(evIter != seqIter->end()) {
//					TrieNode* node = trie.getNodeWithPrefix(*evIter);
//					stream << "eQ!" << node->identifier << "; ";
//					evIter++;
//				}
//				stream << "goto " << sourceName << "NewEvent;" << std::endl;
//				seqIter++;
//			}
//
//			stream << "  " << "  fi;" << std::endl;
//		}
//
//		stream << "  " << "}" << std::endl;
//		stream << "  " << "fi;" << std::endl;
//		stream << sourceName << "Done:" << " skip;" << std::endl;
//		stream << "}" << std::endl;
//
//		i++;
//		sourceIter++;
//	}
}

PromelaEventSource::PromelaEventSource() {
	type = PROMELA_EVENT_SOURCE_INVALID;
	analyzer = NULL;
}

PromelaEventSource::PromelaEventSource(const PromelaInline& source, PromelaCodeAnalyzer* analyzer, uint32_t eQueueLength) {
	type = PROMELA_EVENT_SOURCE_INVALID;
	this->analyzer = analyzer;
	externalQueueLength = eQueueLength;
	
	this->source = source;
	
	if (source.type == PromelaInline::PROMELA_EVENT_SOURCE) {
		std::stringstream ssLines(source.content);
		std::string line;
		while(std::getline(ssLines, line)) {
			boost::trim(line);
			if (line.length() == 0)
				continue;
			if (boost::starts_with(line, "//"))
				continue;

			std::list<std::string> seq;
			std::stringstream ssToken(line);
			std::string token;
			while(std::getline(ssToken, token, ' ')) {
				if (token.length() == 0)
					continue;
				seq.push_back(token);
				if (analyzer != NULL)
					analyzer->addEvent(token);
			}
			sequences.push_back(seq);
			if (seq.size() > longestSequence)
				longestSequence = seq.size();
		}
	}
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
			if (node->operands.front()->type == PML_CMPND)
				node = node->operands.front();
			if (node->operands.front()->type != PML_NAME)
				break; // this will skip array assignments
		case PML_CMPND: {
			std::string nameOfType;
			std::list<PromelaParserNode*>::iterator opIter = node->operands.begin();
			if ((*opIter)->type != PML_NAME) {
				node->dump();
				assert(false);
			}

			_typeDefs.occurrences.insert(interpreter);
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
			_typeDefs.types[node->value].maxValue = 1;
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

void PromelaCodeAnalyzer::addOrigState(const std::string& stateName) {
	if (_origStateIndex.find(stateName) == _origStateIndex.end()) {
		_origStateIndex[stateName] = _lastStateIndex++;
		createMacroName(stateName);
	}
}
	
void PromelaCodeAnalyzer::addState(const std::string& stateName) {
	if (_states.find(stateName) != _states.end())
		return;

	createMacroName(stateName);
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

	_strIndex[literal] = _lastStrIndex++;
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

std::string PromelaCodeAnalyzer::adaptCode(const std::string& code, const std::string& prefix) {
//	for (std::map<std::string, std::string>::const_iterator litIter = _strMacroNames.begin(); litIter != _strMacroNames.end(); litIter++) {
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
			processedStr << code.substr(lastPos, posIter->first - lastPos) << prefix;
			lastPos = posIter->first;
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
			assert(_strMacroNames.find(processed.substr(posIter->first + 1, posIter->second - posIter->first - 2)) != _strMacroNames.end());
			processedStr << _strMacroNames[processed.substr(posIter->first + 1, posIter->second - posIter->first - 2)];
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

//std::string PromelaCodeAnalyzer::prefixIdentifiers(const std::string& expr, const std::string& prefix) {
//	PromelaParser parsed(expr);
//	std::list<size_t> posList = getTokenPositions(expr, PML_NAME, parsed.ast);
//	posList.sort();
//	
//	std::stringstream prefixed;
//	std::list<size_t>::iterator posIter = posList.begin();
//	size_t lastPos = 0;
//	while (posIter != posList.end()) {
//		prefixed << expr.substr(lastPos, *posIter - lastPos) << prefix;
//		lastPos = *posIter;
//		posIter++;
//	}
//	
//	prefixed << expr.substr(lastPos, expr.size() - lastPos);
//	return prefixed.str();
//}
	
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
		posList.merge(tmp);
	}
	return posList;
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

ChartToPromela::~ChartToPromela() {
	if (_analyzer != NULL)
		delete(_analyzer);
	for (std::map<Arabica::DOM::Node<std::string>, ChartToPromela*>::iterator nestedIter = _machines.begin(); nestedIter != _machines.end(); nestedIter++) {
		nestedIter->second->_analyzer = NULL;
		delete (nestedIter->second);
	}
}


void ChartToPromela::writeEvents(std::ostream& stream) {
	std::map<std::string, int> events = _analyzer->getEvents();
	std::map<std::string, int>::iterator eventIter = events.begin();
	stream << "/* event name identifiers */" << std::endl;
	while(eventIter != events.end()) {
		if (eventIter->first.length() > 0) {
			stream << "#define " << _analyzer->macroForLiteral(eventIter->first) << " " << _analyzer->indexForLiteral(eventIter->first);
			stream << " /* from \"" << eventIter->first << "\" */" << std::endl;
		}
		eventIter++;
	}
}

void ChartToPromela::writeStates(std::ostream& stream) {
	stream << "/* state name identifiers */" << std::endl;
	
	std::map<std::string, GlobalState*>::iterator stateIter = _activeConf.begin();
	while(stateIter != _activeConf.end()) {
		stream << "#define " << "s" << stateIter->second->activeIndex << " " << stateIter->second->activeIndex;
		stream << " /* from \"" << stateIter->first << "\" */" << std::endl;
		stateIter++;
	}
	
//	for (int i = 0; i < _globalConf.size(); i++) {
//		stream << "#define " << "s" << i << " " << i;
//		stream << " /* from \"" << ATTR_CAST(_globalStates[i], "id") << "\" */" << std::endl;
//	}
}

void ChartToPromela::writeStateMap(std::ostream& stream) {
	stream << "/* macros for original state names */" << std::endl;
	std::map<std::string, int> origStates = _analyzer->getOrigStates();
	for (std::map<std::string, int>::iterator origIter = origStates.begin(); origIter != origStates.end(); origIter++) {
		stream << "#define " << _analyzer->macroForLiteral(origIter->first) << " " << origIter->second;
		stream << " /* from \"" << origIter->first << "\" */" << std::endl;
	}

//	std::map<std::string, int> states = _analyzer->getStates();
//	size_t stateIndex = 0;
//	for (std::map<std::string, int>::iterator stateIter = states.begin(); stateIter != states.end(); stateIter++) {
//		stream << "_x"
//		std::list<std::string> origStates = _analyzer->getOrigState(stateIter->first);
//		size_t origIndex = 0;
//		for (std::list<std::string>::iterator origIter = origStates.begin(); origIter != origStates.end(); origIter++) {
//
//		}
//	}
}

void ChartToPromela::writeHistoryArrays(std::ostream& stream) {
	stream << "/* history assignments */" << std::endl;
	std::map<std::string, std::map<std::string, size_t> >::iterator histNameIter = _historyMembers.begin();
	while(histNameIter != _historyMembers.end()) {
		stream << "bool _hist_" << boost::to_lower_copy(histNameIter->first) << "[" << histNameIter->second.size() << "];";

		stream << " /* ";
		std::map<std::string, size_t>::iterator histMemberIter = histNameIter->second.begin();
		while(histMemberIter != histNameIter->second.end()) {
			stream << " " << histMemberIter->second << ":" << histMemberIter->first;
			histMemberIter++;
		}
		stream << " */" << std::endl;
		histNameIter++;
	}
}
	
void ChartToPromela::writeTypeDefs(std::ostream& stream) {
	stream << "/* typedefs */" << std::endl;
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
				stream << "  int delay;" << std::endl;
				stream << "  int seqNr;" << std::endl;
			}
			stream << "  int name;" << std::endl;
			if (_analyzer->usesEventField("invokeid")) {
				stream << "  int invokeid;" << std::endl;
			}
		}
		for (std::map<std::string, PromelaCodeAnalyzer::PromelaTypedef>::iterator tIter = currDef.types.begin(); tIter != currDef.types.end(); tIter++) {
			if (currDef.name.compare("_event_t") == 0 && (tIter->first.compare("name") == 0 ||
																										tIter->first.compare("seqNr") == 0 ||
																										tIter->first.compare("invokeid") == 0 ||
																										tIter->first.compare("delay") == 0)) { // special treatment for _event
				continue;
			}
			if (currDef.name.compare("_x_t") == 0 && tIter->first.compare("states") == 0) {
				stream << "  bool states[" << _analyzer->getOrigStates().size() << "];" << std::endl;
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


void ChartToPromela::writeInlineComment(std::ostream& stream, const Arabica::DOM::Node<std::string>& node) {
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

std::string ChartToPromela::conditionForHistoryTransition(const GlobalTransition* transition) {
	FlatStateIdentifier flatSource(transition->source);
	FlatStateIdentifier flatTarget(transition->destination);
	std::string condition;
	
	return condition;
}

std::string ChartToPromela::conditionalizeForHist(GlobalTransition* transition, int indent) {
	std::set<GlobalTransition*> transitions;
	transitions.insert(transition);
	return conditionalizeForHist(transitions);
}
	
std::string ChartToPromela::conditionalizeForHist(const std::set<GlobalTransition*>& transitions, int indent) {
	std::stringstream condition;
	std::string memberSep;
	
	std::set<std::map<std::string, std::list<std::string> > > histSeen;
	
	for (std::set<GlobalTransition*>::const_iterator transIter = transitions.begin(); transIter != transitions.end(); transIter++) {
		if ((*transIter)->histTargets.size() == 0) // there are no history transitions in here!
			continue;
		
		std::map<std::string, std::list<std::string> > relevantHist;
		std::map<std::string, std::list<std::string> > currentHist;
		FlatStateIdentifier flatSource((*transIter)->source);
		currentHist = flatSource.getHistory();
		
		std::set<std::string>::iterator histTargetIter = (*transIter)->histTargets.begin();
		while(histTargetIter != (*transIter)->histTargets.end()) {
			if (currentHist.find(*histTargetIter) != currentHist.end()) {
				relevantHist[*histTargetIter] = currentHist[*histTargetIter];
			}
			histTargetIter++;
		}
		if (relevantHist.size() == 0)
			continue;
		
		if (histSeen.find(relevantHist) != histSeen.end())
			continue;
		histSeen.insert(relevantHist);
		
		std::string itemSep;
		std::map<std::string, std::list<std::string> >::iterator relevanthistIter = relevantHist.begin();

		if (relevantHist.size() > 0)
			condition << memberSep;
		
		while(relevanthistIter != relevantHist.end()) {
			std::list<std::string>::iterator histItemIter = relevanthistIter->second.begin();
			while(histItemIter != relevanthistIter->second.end()) {
				assert(_historyMembers.find(relevanthistIter->first) != _historyMembers.end());
				assert(_historyMembers[relevanthistIter->first].find(*histItemIter) != _historyMembers[relevanthistIter->first].end());
				condition << itemSep << "_hist_" << boost::to_lower_copy(_analyzer->macroForLiteral(relevanthistIter->first)) << "[" << _historyMembers[relevanthistIter->first][*histItemIter] << "]";
				itemSep = " && ";
				histItemIter++;
			}
			relevanthistIter++;
		}

		if (relevantHist.size() > 0)
			memberSep = " || ";

	}
	if (condition.str().size() > 0)
		return "(" + condition.str() + ")";
	return "";
}
	
void ChartToPromela::writeTransition(std::ostream& stream, GlobalTransition* transition, int indent) {
	std::string padding;
	for (int i = 0; i < indent; i++) {
		padding += "  ";
	}

	stream << std::endl << _prefix << "t" << transition->index << ": /* ######################## " << std::endl;
	stream << "   from state: ";
	FlatStateIdentifier flatActiveSource(transition->source);
	PRETTY_PRINT_LIST(stream, flatActiveSource.getActive());
	stream << std::endl;
	stream << "     on event: " << (transition->eventDesc.size() > 0 ? transition->eventDesc : "SPONTANEOUS") << std::endl;
	stream << "############################### */" << std::endl;
	stream << std::endl;

	stream << padding << "atomic {" << std::endl;
//	stream << padding << "  if" << std::endl;
//	stream << padding << "  :: " << _prefix << "done -> goto " << _prefix << "terminate;" << std::endl;
//	stream << padding << "  :: else -> skip;" << std::endl;
//	stream << padding << "  fi" << std::endl;
	padding += "  ";
	indent++;
	
	// iterators of history transitions executable content
	std::map<GlobalTransition*, std::pair<GlobalTransition::Action::iter_t, GlobalTransition::Action::iter_t> > actionIters;
	std::map<GlobalTransition*, std::set<GlobalTransition::Action> > actionsInTransition;
	
	typedef std::map<GlobalTransition*, std::pair<GlobalTransition::Action::iter_t, GlobalTransition::Action::iter_t> > actionIters_t;
	
	std::list<GlobalTransition*>::const_iterator histIter = transition->historyTrans.begin();
	while(histIter != transition->historyTrans.end()) {
		actionIters.insert(std::make_pair((*histIter), std::make_pair((*histIter)->actions.begin(), (*histIter)->actions.end())));
		// add history transitions actions to the set
		std::copy((*histIter)->actions.begin(), (*histIter)->actions.end(), std::inserter(actionsInTransition[*histIter], actionsInTransition[*histIter].begin()));
		histIter++;
	}
	std::copy(transition->actions.begin(), transition->actions.end(), std::inserter(actionsInTransition[transition], actionsInTransition[transition].begin()));
	
	
//	GlobalTransition::Action action;
	std::set<GlobalTransition*> allBut;
	std::list<ExecContentSeqItem> ecSeq;
	
	for (std::list<GlobalTransition::Action>::const_iterator actionIter = transition->actions.begin(); actionIter != transition->actions.end(); actionIter++) {
		// for every executable content in base transition
		const GlobalTransition::Action& baseAction = *actionIter;
		allBut.clear();
		
		for (actionIters_t::iterator histActionIter = actionIters.begin(); histActionIter != actionIters.end(); histActionIter++) {
			// iterate every history transition
			GlobalTransition* histTrans = histActionIter->first;
			GlobalTransition::Action& histAction = *(histActionIter->second.first);

			// is the current action identical?
			if (baseAction != histAction) {
				// executable content differs - will given executable content appear later in history?
				if (actionsInTransition[histTrans].find(baseAction) != actionsInTransition[histTrans].end()) {
					// yes -> write all exec content exclusive to this history transition until base executable content
					while(baseAction != *(histActionIter->second.first)) {
						histAction = *(histActionIter->second.first);
						ecSeq.push_back(ExecContentSeqItem(ExecContentSeqItem::EXEC_CONTENT_ONLY_FOR, histTrans, histAction));
						actionsInTransition[histTrans].erase(histAction);
						histActionIter->second.first++;
					}
				} else {
					// no -> exclude this history transition
					allBut.insert(histTrans);
				}
			} else {
				// that's great, they are equal, just increase iterator
				histActionIter->second.first++;
			}
		}
		
		if (allBut.empty()) {
			// everyone has the current actionIter one behind the base action
			ecSeq.push_back(ExecContentSeqItem(ExecContentSeqItem::EXEC_CONTENT_EVERY, NULL, baseAction));
		} else {
			// everyone but some have this content
			ecSeq.push_back(ExecContentSeqItem(ExecContentSeqItem::EXEC_CONTENT_ALL_BUT, allBut, baseAction));
		}
	}
	
	// see what remains in history transitions and add as exclusive
	for (actionIters_t::iterator histActionIter = actionIters.begin(); histActionIter != actionIters.end(); histActionIter++) {
		GlobalTransition* histTrans = histActionIter->first;

		while(histActionIter->second.first != histActionIter->second.second) {
			GlobalTransition::Action& histAction = *(histActionIter->second.first);
			ecSeq.push_back(ExecContentSeqItem(ExecContentSeqItem::EXEC_CONTENT_ONLY_FOR, histTrans, histAction));
			histActionIter->second.first++;
		}
	}

	bool isConditionalized = false;
	bool wroteHistoryAssignments = false;
	std::set<GlobalTransition*> condSet;
	
	for (std::list<ExecContentSeqItem>::const_iterator ecIter = ecSeq.begin(); ecIter != ecSeq.end(); ecIter++) {
		const GlobalTransition::Action& action = ecIter->action;

		if (action.exited) {
			// first onexit handler writes history assignments
			if (!wroteHistoryAssignments) {
				writeHistoryAssignments(stream, transition, indent);
				wroteHistoryAssignments = true;
			}
		}
		
		if (!_analyzer->usesInPredicate() && (action.entered || action.exited)) {
			continue;
		}
		
		if (ecIter->type == ExecContentSeqItem::EXEC_CONTENT_ONLY_FOR) {
//			assert(!wroteHistoryAssignments); // we need to move assignments after dispatching?
			if (condSet != ecIter->transitions) {
				stream << padding << "if" << std::endl;
				stream << padding << ":: " << conditionalizeForHist(ecIter->transitions) << " -> {" << std::endl;
				padding += "  ";
				indent++;
				isConditionalized = true;
				condSet = ecIter->transitions;
			}
		} else if (ecIter->type == ExecContentSeqItem::EXEC_CONTENT_ALL_BUT) {
//			assert(!wroteHistoryAssignments); // we need to move assignments after dispatching?
			if (condSet != ecIter->transitions) {
				stream << padding << "if" << std::endl;
				stream << padding << ":: " << conditionalizeForHist(ecIter->transitions) << " -> skip;" << std::endl;
				stream << padding << ":: else -> {" << std::endl;
				padding += "  ";
				indent++;
				isConditionalized = true;
				condSet = ecIter->transitions;
			}
		} else {
			isConditionalized = false;
			condSet.clear();
		}

		if (action.exited) {
			// we left a state
			stream << padding << _prefix << "_x.states[" << _analyzer->macroForLiteral(ATTR(action.exited, "id")) << "] = false; " << std::endl;
//			continue;
		}
		
		if (action.entered) {
			// we entered a state
			stream << padding << _prefix << "_x.states[" << _analyzer->macroForLiteral(ATTR(action.entered, "id")) << "] = true; " << std::endl;
//			continue;
		}

		if (action.transition) {
			// this is executable content from a transition
			writeExecutableContent(stream, action.transition, indent);
//			continue;
		}
		
		if (action.onExit) {
			// executable content from an onexit element
			writeExecutableContent(stream, action.onExit, indent);
//			continue;
		}
		
		if (action.onEntry) {
			// executable content from an onentry element
			writeExecutableContent(stream, action.onEntry, indent);
//			continue;
		}
		
		if (action.invoke) {
			// an invoke element
			
			if (_machines.find(action.invoke) != _machines.end()) {
#if 1
				stream << padding << _prefix << "start!" << _analyzer->macroForLiteral(_machines[action.invoke]->_invokerid) << ";" << std::endl;
#else

				// nested SCXML document
				
				// set from namelist
				if (HAS_ATTR_CAST(action.invoke, "namelist")) {
					std::list<std::string> namelist = tokenize(ATTR_CAST(action.invoke, "namelist"));
					for (std::list<std::string>::iterator nlIter = namelist.begin(); nlIter != namelist.end(); nlIter++) {
						if (_machines[action.invoke]->_dataModelVars.find(*nlIter) != _machines[action.invoke]->_dataModelVars.end()) {
							stream << padding << _machines[action.invoke]->_prefix << *nlIter << " = " << _prefix << *nlIter << std::endl;
						}
					}
				}
				
				// set from params
				NodeSet<std::string> invokeParams = filterChildElements(_nsInfo.xmlNSPrefix + "param", action.invoke);
				for (int i = 0; i < invokeParams.size(); i++) {
					std::string identifier = ATTR_CAST(invokeParams[i], "name");
					std::string expression = ATTR_CAST(invokeParams[i], "expr");
					if (_machines[action.invoke]->_dataModelVars.find(identifier) != _machines[action.invoke]->_dataModelVars.end()) {
						stream << padding << _machines[action.invoke]->_prefix << identifier << " = " << ADAPT_SRC(expression) << ";" << std::endl;
					}
				}
				
//				stream << padding << "  /* assign local variables from invoke request */" << std::endl;
//				
//				if (_analyzer->usesComplexEventStruct() && _analyzer->usesEventField("data")) {
//					for (std::set<std::string>::iterator dmIter = _dataModelVars.begin(); dmIter != _dataModelVars.end(); dmIter++) {
//						if (_analyzer->usesEventDataField(*dmIter)) {
//							stream << "  if" << std::endl;
//							stream << "  :: " << _prefix << "_event.data." << *dmIter << " -> " << _prefix << *dmIter << " = " << "_event.data." << *dmIter << ";" << std::endl;
//							stream << "  :: else -> skip;" << std::endl;
//							stream << "  fi" << std::endl;
//						}
//					}
//				}
//				stream << std::endl;

				stream << padding << "run " << _machines[action.invoke]->_prefix << "run() priority 20;" << std::endl;
				if (HAS_ATTR_CAST(action.invoke, "idlocation")) {
					stream << padding << ADAPT_SRC(ATTR_CAST(action.invoke, "idlocation")) << " = " << _analyzer->macroForLiteral(_machines[_machinesPerId[ATTR_CAST(action.invoke, "id")]]->_invokerid) << ";" << std::endl;
				}
#endif
			} else {
				if (HAS_ATTR_CAST(action.invoke, "invokeid") && _invokers.find(ATTR_CAST(action.invoke, "invokeid")) != _invokers.end())
					_invokers[ATTR_CAST(action.invoke, "invokeid")].writeStart(stream, indent);
			}

		}
		
		if (action.uninvoke) {
			assert(_machines.find(action.uninvoke) != _machines.end());
			stream << padding << "do" << std::endl;
			stream << padding << ":: " << _prefix << "start??" << _analyzer->macroForLiteral(_machines[action.uninvoke]->_invokerid) << " -> skip" << std::endl;
			stream << padding << ":: else -> break;" << std::endl;
			stream << padding << "od" << std::endl;

//			std::cout << action.uninvoke << std::endl;
			// an invoke element to uninvoke
			if (_machines.find(action.uninvoke) != _machines.end()) {
				// nested SCXML document
				stream << padding << _machines[action.uninvoke]->_prefix << "canceled = true;" << std::endl;
				writeRemovePendingEventsFromInvoker(stream, _machines[action.uninvoke], indent, false);
#if 0
				stream << padding << "do" << std::endl;
				stream << padding << ":: len(" << _machines[action.uninvoke]->_prefix << "tmpQ) > 0 -> " << _machines[action.uninvoke]->_prefix << "tmpQ?_;" << std::endl;
				stream << padding << ":: len(" << _machines[action.uninvoke]->_prefix << "eQ) > 0 -> " << _machines[action.uninvoke]->_prefix << "eQ?_;" << std::endl;
				stream << padding << ":: else -> break;" << std::endl;
				stream << padding << "od" << std::endl;
#endif
			} else {
				if (HAS_ATTR_CAST(action.uninvoke, "invokeid") && _invokers.find(ATTR_CAST(action.invoke, "invokeid")) != _invokers.end())
					stream << padding << ATTR_CAST(action.uninvoke, "invokeid") << "EventSourceDone" << "= 1;" << std::endl;
			}
//			continue;
		}
		
		if (isConditionalized) {
			padding = padding.substr(2);
			indent--;
			if (ecIter->type == ExecContentSeqItem::EXEC_CONTENT_ALL_BUT) {
				stream << padding << "}" << std::endl;
				stream << padding << "fi" << std::endl;
			} else if(ecIter->type == ExecContentSeqItem::EXEC_CONTENT_ONLY_FOR) {
				stream << padding << "}" << std::endl;
				stream << padding << ":: else -> skip;" << std::endl;
				stream << padding << "fi;" << std::endl;
			}
			isConditionalized = false;
		}
	}
	
	if (!wroteHistoryAssignments) {
		writeHistoryAssignments(stream, transition, indent);
		wroteHistoryAssignments = true;
	}

	// write new state assignment and goto dispatching
	GlobalState* origNewState = NULL;

	// sort history transitions by new active state
	std::map<GlobalState*, std::set<GlobalTransition*> > histTargets;
	histIter = transition->historyTrans.begin();
	while(histIter != transition->historyTrans.end()) {
		origNewState = _activeConf[(*histIter)->activeDestination];
		assert(origNewState != NULL);
		histTargets[origNewState].insert(*histIter);
		histIter++;
	}

	origNewState = _activeConf[transition->activeDestination];
	bool hasHistoryTarget = false;
	
	for (std::map<GlobalState*, std::set<GlobalTransition*> >::const_iterator histTargetIter = histTargets.begin(); histTargetIter != histTargets.end(); histTargetIter++) {
		GlobalState* histNewState = histTargetIter->first;
		if (histNewState == origNewState)
			continue;
		stream << padding << "if" << std::endl;
		stream << padding << "::" << conditionalizeForHist(histTargetIter->second) << " -> {" << std::endl;
		stream << std::endl << "/* via hist ";
		FlatStateIdentifier flatActiveDest(histNewState->activeId);
		PRETTY_PRINT_LIST(stream, flatActiveDest.getActive());
		stream << "*/" << std::endl;

		stream << padding << "  " << _prefix << "s = s" << histNewState->activeIndex << ";" << std::endl;
		
		writeTransitionClosure(stream, *histTargetIter->second.begin(), histNewState, indent + 1); // is this correct for everyone in set?

		stream << padding << "}" << std::endl;
		hasHistoryTarget = true;
	}
	
	if (hasHistoryTarget) {
		stream << padding << ":: else {" << std::endl;
		padding += "  ";
		indent++;
	}
	
	origNewState = _activeConf[transition->activeDestination];
	assert(origNewState != NULL);
	
	
	stream << std::endl << "/* to state ";
	FlatStateIdentifier flatActiveDest(transition->activeDestination);
	PRETTY_PRINT_LIST(stream, flatActiveDest.getActive());
	stream <<  " */" << std::endl;
	
	stream << padding << _prefix << "s = s" << origNewState->activeIndex << ";" << std::endl;

	writeTransitionClosure(stream, transition, origNewState, indent);

	if (hasHistoryTarget) {
		padding = padding.substr(2);
		indent--;
		stream << padding << "}" << std::endl;
		stream << padding << "fi;" << std::endl;
	}
	
	padding = padding.substr(2);
	stream << padding << "}" << std::endl;

}

void ChartToPromela::writeHistoryAssignments(std::ostream& stream, GlobalTransition* transition, int indent) {
	std::string padding;
	for (int i = 0; i < indent; i++) {
		padding += "  ";
	}
	
	// GlobalState to *changed* history configuration
	std::list<HistoryTransitionClass> histClasses;

	std::set<GlobalTransition*> allTrans;
	allTrans.insert(transition);
	allTrans.insert(transition->historyTrans.begin(), transition->historyTrans.end());
	
	// iterate all transitions
	std::set<GlobalTransition*>::iterator transIter = allTrans.begin();
	while(transIter != allTrans.end()) {
		histClasses.push_back(HistoryTransitionClass(*transIter));
		transIter++;
	}
	
	// nothing to do here
	if (histClasses.size() == 0)
		return;
	
//	std::cout << histClasses.size() << " / ";
	
	// now sort into equivalence classes
	std::list<HistoryTransitionClass>::iterator outerHistClassIter = histClasses.begin();
	std::list<HistoryTransitionClass>::iterator innerHistClassIter = histClasses.begin();
	while(outerHistClassIter != histClasses.end()) {
		HistoryTransitionClass& outerClass = *outerHistClassIter;

		// iterate inner iter for every outer iter and see if we can merge
		innerHistClassIter = outerHistClassIter;
		innerHistClassIter++;
		
		while(innerHistClassIter != histClasses.end()) {
			// can we merge the inner class into the outer one?
			HistoryTransitionClass& innerClass = *innerHistClassIter;
			
			if (outerClass.matches(innerClass)) {
				outerClass.merge(innerClass);
				histClasses.erase(innerHistClassIter);
			}
			
			innerHistClassIter++;
		}
		outerHistClassIter++;
	}
//	std::cout << histClasses.size() << std::endl;

	bool preambelWritten = false;
	std::list<HistoryTransitionClass>::iterator histClassIter = histClasses.begin();
	std::list<HistoryTransitionClass>::iterator defaultHistClassIter = histClasses.end();
	size_t nrMembers = 0;
	while(histClassIter != histClasses.end() || defaultHistClassIter != histClasses.end()) {

		// remember iterator position with default transition
		if (histClassIter == histClasses.end() && defaultHistClassIter != histClasses.end()) {
			histClassIter = defaultHistClassIter;
		} else if (histClassIter->members.find(transition) != histClassIter->members.end()) {
			defaultHistClassIter = histClassIter;
			histClassIter++;
			continue;
		}

		nrMembers += histClassIter->members.size();

		if (!preambelWritten && histClasses.size() > 1) {
			stream << padding << "if" << std::endl;
			preambelWritten = true;
		}

		if (histClasses.size() > 1) {
			stream << padding << "::" << conditionalizeForHist(histClassIter->members) << " {" << std::endl;
		}

		{
			std::map<std::string, std::set<std::string> >::iterator forgetIter = histClassIter->toForget.begin();
			while(forgetIter != histClassIter->toForget.end()) {
				std::set<std::string>::iterator forgetMemberIter = forgetIter->second.begin();
				while(forgetMemberIter != forgetIter->second.end()) {
					stream << padding << "_hist_" << boost::to_lower_copy(_analyzer->macroForLiteral(forgetIter->first));
					stream << "[" << _historyMembers[forgetIter->first][*forgetMemberIter] << "] = 0;";
					stream << " \t/* " << *forgetMemberIter << " */" << std::endl;
					forgetMemberIter++;
				}
				forgetIter++;
			}
		}
		
		{
			std::map<std::string, std::set<std::string> >::iterator rememberIter = histClassIter->toRemember.begin();
			while(rememberIter != histClassIter->toRemember.end()) {
				std::set<std::string>::iterator rememberMemberIter = rememberIter->second.begin();
				while(rememberMemberIter != rememberIter->second.end()) {
					stream << padding << "_hist_" << boost::to_lower_copy(_analyzer->macroForLiteral(rememberIter->first));
					stream << "[" << _historyMembers[rememberIter->first][*rememberMemberIter] << "] = 1;";
					stream << " \t/* " << *rememberMemberIter << " */" << std::endl;
					rememberMemberIter++;
				}
				rememberIter++;
			}
		}

		if (histClasses.size() > 1) {
			stream << padding << "}" << std::endl;
		}

		if (histClassIter == defaultHistClassIter) {
			break;
		}
		
		histClassIter++;
	}
	assert(nrMembers == allTrans.size());
	
}

HistoryTransitionClass::HistoryTransitionClass(GlobalTransition* transition) {
	members.insert(transition);
	init(transition->source, transition->destination);
}

HistoryTransitionClass::HistoryTransitionClass(const std::string& from, const std::string& to) {
	init(from, to);
}

void HistoryTransitionClass::init(const std::string& from, const std::string& to) {
	FlatStateIdentifier flatSource(from);
	FlatStateIdentifier flatTarget(to);
	
	std::map<std::string, std::set<std::string> > activeBefore = flatSource.getHistorySets();
	std::map<std::string, std::set<std::string> > activeAfter = flatTarget.getHistorySets();
	
	std::map<std::string, std::set<std::string> >::const_iterator targetHistIter = activeAfter.begin();
	while(targetHistIter != activeAfter.end()) {
		// for every history state in target, see if it existed in source
		if (activeBefore.find(targetHistIter->first) == activeBefore.end()) {
			// this target history did not exist source -> every item is changed
			std::set<std::string>::const_iterator histMemberIter = activeAfter.at(targetHistIter->first).begin();
			while(histMemberIter != activeAfter.at(targetHistIter->first).end()) {
				toRemember[targetHistIter->first].insert(*histMemberIter);
				histMemberIter++;
			}
		} else {
			// this target *did* already exist, but was it equally assigned?
			std::set<std::string>::const_iterator sourceHistMemberIter = activeBefore.at(targetHistIter->first).begin();
			while(sourceHistMemberIter != activeBefore.at(targetHistIter->first).end()) {
				// iterate every item in source and try to find it in target
				if (targetHistIter->second.find(*sourceHistMemberIter) == targetHistIter->second.end()) {
					// no, source is no longer in target
					toForget[targetHistIter->first].insert(*sourceHistMemberIter);
				} else {
					toKeep[targetHistIter->first].insert(*sourceHistMemberIter);
				}
				sourceHistMemberIter++;
			}
			
			std::set<std::string>::const_iterator targetHistMemberIter = activeAfter.at(targetHistIter->first).begin();
			while(targetHistMemberIter != activeAfter.at(targetHistIter->first).end()) {
				// iterate member of target history and see if it is new
				if (activeBefore.at(targetHistIter->first).find(*targetHistMemberIter) == activeBefore.at(targetHistIter->first).end()) {
					// not found -> new assignment
					toRemember[targetHistIter->first].insert(*targetHistMemberIter);
				}
				targetHistMemberIter++;
			}
		}
		targetHistIter++;
	}
}
	
bool HistoryTransitionClass::matches(const HistoryTransitionClass& other) {

	/* does the given transition match this one?:
	 1. everything remembered has to be remembered as well or already enabled
	 2. everything forgot has to be forgotten as well or already disabled
	 and vice versa
	 */
	
	std::map<std::string, std::set<std::string> > tmp;
	
	typedef std::map<std::string, std::set<std::string> >::const_iterator histIter_t;
	typedef std::set<std::string>::const_iterator histMemberIter_t;
	
	// we will remember these - will the other try to forget them?
	INTERSECT_MAPS(toRemember, other.toForget, tmp);
	if (tmp.size() > 0)
		return false;

	// we will keep these - will the other try to forget them?
	INTERSECT_MAPS(toKeep, other.toForget, tmp);
	if (tmp.size() > 0)
		return false;

	// we will forget these - will the other try to keep or even remember?
	INTERSECT_MAPS(toForget, other.toKeep, tmp);
	if (tmp.size() > 0)
		return false;
	INTERSECT_MAPS(toForget, other.toRemember, tmp);
	if (tmp.size() > 0)
		return false;

	return true;
}

void HistoryTransitionClass::merge(const HistoryTransitionClass& other) {
	members.insert(other.members.begin(), other.members.end());
	
	std::map<std::string, std::set<std::string> >::const_iterator histIter;
	
	histIter = other.toRemember.begin();
	while(histIter != other.toRemember.end()) {
		toRemember[histIter->first].insert(histIter->second.begin(), histIter->second.end());
		histIter++;
	}

	histIter = other.toForget.begin();
	while(histIter != other.toForget.end()) {
		toForget[histIter->first].insert(histIter->second.begin(), histIter->second.end());
		histIter++;
	}

	histIter = other.toKeep.begin();
	while(histIter != other.toKeep.end()) {
		toKeep[histIter->first].insert(histIter->second.begin(), histIter->second.end());
		histIter++;
	}

}
	
void ChartToPromela::writeTransitionClosure(std::ostream& stream, GlobalTransition* transition, GlobalState* state, int indent) {
	std::string padding;
	for (int i = 0; i < indent; i++) {
		padding += "  ";
	}

	if (state->isFinal) {
		stream << padding << "goto " << _prefix << "terminate;" << std::endl;
	} else {
		if (!transition->isEventless) {
			stream << padding << _prefix << "spontaneous = true;" << std::endl;
		}
		stream << padding << "goto " << _prefix << "microStep;" << std::endl;
	}
}

void ChartToPromela::writeExecutableContent(std::ostream& stream, const Arabica::DOM::Node<std::string>& node, int indent) {
	if (!node)
		return;

	std::string padding;
	for (int i = 0; i < indent; i++) {
		padding += "  ";
	}

	if (node.getNodeType() == Node_base::COMMENT_NODE) {
		// we cannot have labels in an atomic block, just process inline promela
		PromelaInlines promInls = PromelaInlines::fromNode(node);
		//		TODO!
		//		if (promInls) {
		//		stream << padding << "skip;" << std::endl;
		//		stream << beautifyIndentation(inlinePromela.str(), indent) << std::endl;
		//		}
	}

	if (node.getNodeType() == Node_base::TEXT_NODE) {
		if (boost::trim_copy(node.getNodeValue()).length() > 0)
			stream << beautifyIndentation(ADAPT_SRC(node.getNodeValue()), indent) << std::endl;
	}
	
	if (node.getNodeType() != Node_base::ELEMENT_NODE)
		return; // skip anything not an element

	Arabica::DOM::Element<std::string> nodeElem = Arabica::DOM::Element<std::string>(node);

	if (false) {
	} else if(TAGNAME(nodeElem) == "onentry" || TAGNAME(nodeElem) == "onexit" || TAGNAME(nodeElem) == "transition" || TAGNAME(nodeElem) == "finalize") {
		// descent into childs and write their contents
		Arabica::DOM::Node<std::string> child = node.getFirstChild();
		while(child) {
			writeExecutableContent(stream, child, indent);
			child = child.getNextSibling();
		}
	} else if(TAGNAME(nodeElem) == "script") {
		NodeSet<std::string> scriptText = filterChildType(Node_base::TEXT_NODE, node, true);
		for (int i = 0; i < scriptText.size(); i++) {
			stream << ADAPT_SRC(beautifyIndentation(scriptText[i].getNodeValue(), indent)) << std::endl;
		}
		
	} else if(TAGNAME(nodeElem) == "log") {
		std::string label = (HAS_ATTR(nodeElem, "label") ? ATTR(nodeElem, "label") : "");
		std::string expr = (HAS_ATTR(nodeElem, "expr") ? ADAPT_SRC(ATTR(nodeElem, "expr")) : "");
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
		stream << padding << "for (" << _prefix << (HAS_ATTR(nodeElem, "index") ? ATTR(nodeElem, "index") : "_index") << " in " << _prefix << ATTR(nodeElem, "array") << ") {" << std::endl;
		if (HAS_ATTR(nodeElem, "item")) {
			stream << padding << "  " << _prefix << ATTR(nodeElem, "item") << " = " << _prefix << ATTR(nodeElem, "array") << "[" << _prefix << (HAS_ATTR(nodeElem, "index") ? ATTR(nodeElem, "index") : "_index") << "];" << std::endl;
		}
		Arabica::DOM::Node<std::string> child = node.getFirstChild();
		while(child) {
			writeExecutableContent(stream, child, indent + 1);
			child = child.getNextSibling();
		}
		if (HAS_ATTR(nodeElem, "index"))
			stream << padding << "  " << _prefix << ATTR(nodeElem, "index") << "++;" << std::endl;
		stream << padding << "}" << std::endl;
		
	} else if(TAGNAME(nodeElem) == "if") {
		NodeSet<std::string> condChain;
		condChain.push_back(node);
		condChain.push_back(filterChildElements(_nsInfo.xmlNSPrefix + "elseif", node));
		condChain.push_back(filterChildElements(_nsInfo.xmlNSPrefix + "else", node));
		
		writeIfBlock(stream, condChain, indent);
		
	} else if(TAGNAME(nodeElem) == "assign") {
		NodeSet<std::string> assignTexts = filterChildType(Node_base::TEXT_NODE, nodeElem, true);
		assert(assignTexts.size() > 0);
		stream << ADAPT_SRC(boost::trim_copy(assignTexts[0].getNodeValue())) << std::endl;
		
	} else if(TAGNAME(nodeElem) == "send" || TAGNAME(nodeElem) == "raise") {
		std::string targetQueue;
		if (TAGNAME(nodeElem) == "raise") {
			targetQueue = _prefix + "iQ!";
		} else if (!HAS_ATTR(nodeElem, "target")) {
			targetQueue = _prefix + "tmpQ!";
		} else if (ATTR(nodeElem, "target").compare("#_internal") == 0) {
			targetQueue = _prefix + "iQ!";
		} else if (ATTR(nodeElem, "target").compare("#_parent") == 0) {
			targetQueue = _parent->_prefix + "eQ!";
		} else if (boost::starts_with(ATTR(nodeElem, "target"), "#_") && _machinesPerId.find(ATTR(nodeElem, "target").substr(2)) != _machinesPerId.end()) {
			targetQueue = _machines[_machinesPerId[ATTR(nodeElem, "target").substr(2)]]->_prefix + "eQ!";
		}
		if (targetQueue.length() > 0) {
			// this is for our external queue
			std::string event;
			
			if (HAS_ATTR(nodeElem, "event")) {
				event = _analyzer->macroForLiteral(ATTR(nodeElem, "event"));
			} else if (HAS_ATTR(nodeElem, "eventexpr")) {
				event = ADAPT_SRC(ATTR(nodeElem, "eventexpr"));
			}
			if (_analyzer->usesComplexEventStruct()) {
				stream << padding << "{" << std::endl;
				stream << padding << "  _event_t tmpE;" << std::endl;
				stream << padding << "  tmpE.name = " << event << ";" << std::endl;
				
				if (HAS_ATTR(nodeElem, "idlocation")) {
					stream << padding << "  /* idlocation */" << std::endl;
					stream << padding << "  _lastSendId = _lastSendId + 1;" << std::endl;
					stream << padding << "  " << _prefix << ATTR(nodeElem, "idlocation") << " = _lastSendId;" << std::endl;
					stream << padding << "  tmpE.sendid = _lastSendId;" << std::endl;
					stream << padding << "  if" << std::endl;
					stream << padding << "  :: _lastSendId == 2147483647 -> _lastSendId = 0;" << std::endl;
					stream << padding << "  :: timeout -> skip;" << std::endl;
					stream << padding << "  fi;" << std::endl;
				} else if (HAS_ATTR(nodeElem, "id")) {
					stream << padding << "  tmpE.sendid = " << _analyzer->macroForLiteral(ATTR(nodeElem, "id")) << ";" << std::endl;
				}
				
				if (_invokerid.length() > 0 && !boost::starts_with(targetQueue, _prefix)) { // do not send invokeid if we send / raise to ourself
					stream << padding << "  tmpE.invokeid = " << _analyzer->macroForLiteral(_invokerid) << ";" << std::endl;
				}
				
				if (_analyzer->usesEventField("origintype") && !boost::ends_with(targetQueue, "iQ!")) {
					stream << padding << "  tmpE.origintype = " << _analyzer->macroForLiteral("http://www.w3.org/TR/scxml/#SCXMLEventProcessor") << ";" << std::endl;
				}

				if (_analyzer->usesEventField("delay")) {
					targetQueue += "!";
					stream << padding << "  _lastSeqId = _lastSeqId + 1;" << std::endl;
					if (HAS_ATTR_CAST(nodeElem, "delay")) {
						stream << padding << "  tmpE.delay = " << ATTR_CAST(nodeElem, "delay") << ";" << std::endl;
					} else if (HAS_ATTR_CAST(nodeElem, "delayexpr")) {
						stream << padding << "  tmpE.delay = " << ADAPT_SRC(ATTR_CAST(nodeElem, "delayexpr")) << ";" << std::endl;
					} else {
						stream << padding << "  tmpE.delay = 0;" << std::endl;
					}
					stream << padding << "  tmpE.seqNr = _lastSeqId;" << std::endl;
				}

				if (_analyzer->usesEventField("type")) {
					std::string eventType = (targetQueue.compare("iQ!") == 0 ? _analyzer->macroForLiteral("internal") : _analyzer->macroForLiteral("external"));
					stream << padding << "  tmpE.type = " << eventType << ";" << std::endl;
				}
				
				NodeSet<std::string> sendParams = filterChildElements(_nsInfo.xmlNSPrefix + "param", nodeElem);
				NodeSet<std::string> sendContents = filterChildElements(_nsInfo.xmlNSPrefix + "content", nodeElem);
				std::string sendNameList = ATTR(nodeElem, "namelist");
				if (sendParams.size() > 0) {
					for (int i = 0; i < sendParams.size(); i++) {
						Element<std::string> paramElem = Element<std::string>(sendParams[i]);
						stream << padding << "  tmpE.data." << ATTR(paramElem, "name") << " = " << ADAPT_SRC(ATTR(paramElem, "expr"))  << ";" << std::endl;
					}
				}
				if (sendNameList.size() > 0) {
					std::list<std::string> nameListIds = tokenizeIdRefs(sendNameList);
					std::list<std::string>::iterator nameIter = nameListIds.begin();
					while(nameIter != nameListIds.end()) {
						stream << padding << "  tmpE.data." << *nameIter << " = " << ADAPT_SRC(*nameIter) << ";" << std::endl;
						nameIter++;
					}
				}
				
				if (sendParams.size() == 0 && sendNameList.size() == 0 && sendContents.size() > 0) {
					Element<std::string> contentElem = Element<std::string>(sendContents[0]);
					if (contentElem.hasChildNodes() && contentElem.getFirstChild().getNodeType() == Node_base::TEXT_NODE) {
						std::string content = spaceNormalize(contentElem.getFirstChild().getNodeValue());
						if (!isNumeric(content.c_str(), 10)) {
							stream << padding << "  tmpE.data = " << _analyzer->macroForLiteral(content) << ";" << std::endl;
						} else {
							stream << padding << "  tmpE.data = " << content << ";" << std::endl;
						}
					} else if (HAS_ATTR(contentElem, "expr")) {
						stream << padding << "  tmpE.data = " << ADAPT_SRC(ATTR(contentElem, "expr")) << ";" << std::endl;
					}
				}
				stream << padding << "  " << targetQueue << "tmpE;" << std::endl;
				stream << padding << "}" << std::endl;
			} else {
				stream << padding << targetQueue << event << ";" << std::endl;
			}
		}
	} else if(TAGNAME(nodeElem) == "cancel") {
		writeCancelWithIdOrExpr(stream, nodeElem, this, indent);
	} else {
		std::cerr << "'" << TAGNAME(nodeElem) << "'" << std::endl << nodeElem << std::endl;
		assert(false);
	}
}

void ChartToPromela::writeCancelWithIdOrExpr(std::ostream& stream, const Arabica::DOM::Element<std::string>& cancel, ChartToPromela* invoker, int indent) {
	std::string padding;
	for (int i = 0; i < indent; i++) {
		padding += "  ";
	}

	ChartToPromela* topMachine = (invoker->_parent != NULL ? invoker->_parent : invoker);
	
	std::list<ChartToPromela*> others;
	others.push_back(topMachine);
	for (std::map<Arabica::DOM::Node<std::string>, ChartToPromela*>::iterator queueIter = topMachine->_machines.begin(); queueIter != topMachine->_machines.end(); queueIter++) {
		others.push_back(queueIter->second);
	}
	
	if (HAS_ATTR(cancel, "sendid")) {
		stream << padding << "/* cancel event given by sendid */" << std::endl;
		stream << padding << "atomic {" << std::endl;
		stream << padding << "  _event_t tmpE;" << std::endl;
		stream << padding << "  do" << std::endl;
		for (std::list<ChartToPromela*>::iterator queueIter = others.begin(); queueIter != others.end(); queueIter++) {
			stream << padding << "  :: " << (*queueIter)->_prefix << "eQ?\?" << (_analyzer->usesEventField("delay") ? "tmpE.delay, tmpE.seqNr," : "") << " tmpE.name, " << _analyzer->macroForLiteral(ATTR(cancel, "sendid")) << ";" << std::endl;
			stream << padding << "  :: " << (*queueIter)->_prefix << "tmpQ?\?" << (_analyzer->usesEventField("delay") ? "tmpE.delay, tmpE.seqNr," : "") << " tmpE.name, " << _analyzer->macroForLiteral(ATTR(cancel, "sendid")) << ";" << std::endl;
		}
		stream << padding << "  :: else -> break;" << std::endl;
		stream << padding << "  od" << std::endl;
		stream << padding << "}" << std::endl;

	} else if (HAS_ATTR(cancel, "sendidexpr")) {
		stream << padding << "/* cancel event given by sendidexpr */" << std::endl;
		stream << padding << "atomic {" << std::endl;
		stream << padding << "  _event_t tmpE;" << std::endl;
		
		stream << padding << "  do" << std::endl;
		stream << padding << "  :: (len(" << _prefix << "tmpQ) > 0) -> { " << _prefix << "tmpQ?tmpE; sendIdQ!tmpE;  }" << std::endl;
		stream << padding << "  :: else -> break;" << std::endl;
		stream << padding << "  od" << std::endl;
		
		stream << padding << "  do" << std::endl;
		stream << padding << "  :: (len(sendIdQ) > 0) -> {" << std::endl;
		stream << padding << "    sendIdQ?tmpE;" << std::endl;
		stream << padding << "    if" << std::endl;
		stream << padding << "    :: (tmpE.sendid != " << ADAPT_SRC(ATTR(cancel, "sendidexpr")) << ") -> " << _prefix << "tmpQ!tmpE" << std::endl;
		stream << padding << "    :: else -> skip;" << std::endl;
		stream << padding << "    fi" << std::endl;
		stream << padding << "  }" << std::endl;
		stream << padding << "  :: else -> break;" << std::endl;
		stream << padding << "  od" << std::endl;

		for (std::list<ChartToPromela*>::iterator queueIter = others.begin(); queueIter != others.end(); queueIter++) {
			stream << padding << "  do" << std::endl;
			stream << padding << "  :: (len(" << (*queueIter)->_prefix << "eQ) > 0) -> { " << (*queueIter)->_prefix << "eQ?tmpE; sendIdQ!tmpE;  }" << std::endl;
			stream << padding << "  :: else -> break;" << std::endl;
			stream << padding << "  od" << std::endl;
			
			stream << padding << "  do" << std::endl;
			stream << padding << "  :: (len(sendIdQ) > 0) -> {" << std::endl;
			stream << padding << "    sendIdQ?tmpE;" << std::endl;
			stream << padding << "    if" << std::endl;
			stream << padding << "    :: (tmpE.sendid != " << ADAPT_SRC(ATTR(cancel, "sendidexpr")) << ") -> " << (*queueIter)->_prefix << "eQ!tmpE" << std::endl;
			stream << padding << "    :: else -> skip;" << std::endl;
			stream << padding << "    fi" << std::endl;
			stream << padding << "  }" << std::endl;
			stream << padding << "  :: else -> break;" << std::endl;
			stream << padding << "  od" << std::endl;
		}
		stream << padding << "}" << std::endl;
	}

}

PromelaInlines PromelaInlines::fromNodeSet(const NodeSet<std::string>& node, bool recurse) {
	PromelaInlines allPromInls;
	Arabica::XPath::NodeSet<std::string> comments = InterpreterImpl::filterChildType(Node_base::COMMENT_NODE, node, recurse);
	for (int i = 0; i < comments.size(); i++) {
		allPromInls.merge(PromelaInlines::fromNode(comments[i]));
	}
	return allPromInls;
	
}

PromelaInlines PromelaInlines::fromNode(const Arabica::DOM::Node<std::string>& node) {
	if (node.getNodeType() != Node_base::COMMENT_NODE && node.getNodeType() != Node_base::TEXT_NODE)
		return PromelaInlines();
	return PromelaInlines(node.getNodeValue(), node);
}

	PromelaInlines PromelaInlines::fromString(const std::string& text) {
	return PromelaInlines(text, Arabica::DOM::Node<std::string>());
}

PromelaInlines::PromelaInlines() : nrProgressLabels(0), nrAcceptLabels(0), nrEndLabels(0), nrEventSources(0), nrCodes(0) {
}

PromelaInlines::PromelaInlines(const std::string& content, const Arabica::DOM::Node<std::string>& node)
		: nrProgressLabels(0), nrAcceptLabels(0), nrEndLabels(0), nrEventSources(0), nrCodes(0) {

	std::stringstream ssLine(content);
	std::string line;

	bool isInPromelaCode = false;
	PromelaInline promInl;

	while(std::getline(ssLine, line)) {
		std::string trimLine = boost::trim_copy(line);
		if (trimLine.length() == 0)
			continue;
		if (boost::starts_with(trimLine, "#promela")) {
			if (isInPromelaCode) {
				code.push_back(promInl);
				isInPromelaCode = false;
			}
			promInl = PromelaInline();
		}

		if (false) {
		} else if (boost::starts_with(trimLine, "#promela-progress")) {
			nrProgressLabels++;
			promInl.type = PromelaInline::PROMELA_PROGRESS_LABEL;
			promInl.content = line;
			code.push_back(promInl);
		} else if (boost::starts_with(trimLine, "#promela-accept")) {
			nrAcceptLabels++;
			promInl.type = PromelaInline::PROMELA_ACCEPT_LABEL;
			promInl.content = line;
			code.push_back(promInl);
		} else if (boost::starts_with(trimLine, "#promela-end")) {
			nrEndLabels++;
			promInl.type = PromelaInline::PROMELA_END_LABEL;
			promInl.content = line;
			code.push_back(promInl);
		} else if (boost::starts_with(trimLine, "#promela-inline")) {
			nrCodes++;
			isInPromelaCode = true;
			promInl.type = PromelaInline::PROMELA_CODE;
		} else if (boost::starts_with(trimLine, "#promela-event-source-custom")) {
			nrEventSources++;
			isInPromelaCode = true;
			promInl.type = PromelaInline::PROMELA_EVENT_SOURCE_CUSTOM;
		} else if (boost::starts_with(trimLine, "#promela-event-source")) {
			nrEventSources++;
			isInPromelaCode = true;
			promInl.type = PromelaInline::PROMELA_EVENT_SOURCE;
		} else if (isInPromelaCode) {
			promInl.content += line;
			promInl.content += "\n";
		}
	}
	// inline code ends with comment
	if (isInPromelaCode) {
		code.push_back(promInl);
	}
			
	// iterate inlinesFound and classify
//			PromelaEventSource promES; // TODO! use this

}

void ChartToPromela::writeIfBlock(std::ostream& stream, const Arabica::XPath::NodeSet<std::string>& condChain, int indent) {
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
	stream << padding << ":: (" << ADAPT_SRC(ATTR(ifNode, "cond")) << ") -> {" << std::endl;

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


std::string ChartToPromela::beautifyIndentation(const std::string& code, int indent) {

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

void ChartToPromela::writeStrings(std::ostream& stream) {
	stream << "/* string literals */" << std::endl;
	std::set<std::string> literals = _analyzer->getLiterals();
	std::map<std::string, int> events = _analyzer->getEvents();
	std::map<std::string, int> origStates = _analyzer->getOrigStates();

	for (std::set<std::string>::const_iterator litIter = literals.begin(); litIter != literals.end(); litIter++) {
		if (events.find(*litIter) == events.end() && (origStates.find(*litIter) == origStates.end() || !_analyzer->usesInPredicate()))
			stream << "#define " << _analyzer->macroForLiteral(*litIter) << " " << _analyzer->indexForLiteral(*litIter) << " /* " << *litIter << " */" << std::endl;
	}
}

void ChartToPromela::writeDeclarations(std::ostream& stream) {

	stream << "/* global variables */" << std::endl;
	
	// we cannot know our event queue with nested invokers? Adding some for test422
	size_t tolerance = 6;
	
	if (_analyzer->usesComplexEventStruct()) {
		// event is defined with the typedefs
		stream << "_event_t " << _prefix << "_event;               /* current event */" << std::endl;
		stream << "unsigned " << _prefix << "s : " << BIT_WIDTH(_activeConf.size() + 1) << ";                /* current state */" << std::endl;
		stream << "chan " << _prefix << "iQ   = [" << MAX(_internalQueueLength, 1) << "] of {_event_t}  /* internal queue */" << std::endl;
		stream << "chan " << _prefix << "eQ   = [" << _externalQueueLength + tolerance << "] of {_event_t}  /* external queue */" << std::endl;
		stream << "chan " << _prefix << "tmpQ = [" << MAX(_externalQueueLength + tolerance, 1) << "] of {_event_t}  /* temporary queue for external events in transitions */" << std::endl;
//		stream << "hidden " << "_event_t " << _prefix << "tmpQItem;" << std::endl;
	} else {
		stream << "unsigned " << _prefix << "_event : " << BIT_WIDTH(_analyzer->getEvents().size() + 1) << ";                /* current event */" << std::endl;
		stream << "unsigned " << _prefix << "s : " << BIT_WIDTH(_activeConf.size() + 1) << ";            /* current state */" << std::endl;
		stream << "chan " << _prefix << "iQ   = [" << MAX(_internalQueueLength, 1) << "] of {int}  /* internal queue */" << std::endl;
		stream << "chan " << _prefix << "eQ   = [" << _externalQueueLength + tolerance << "] of {int}  /* external queue */" << std::endl;
		stream << "chan " << _prefix << "tmpQ = [" << MAX(_externalQueueLength + tolerance, 1) << "] of {int}  /* temporary queue for external events in transitions */" << std::endl;
//		stream << "hidden unsigned " << _prefix << "tmpQItem : " << BIT_WIDTH(_analyzer->getEvents().size() + 1) << ";" << std::endl;
	}
	if (_machines.size() > 0) {
		stream << "chan " << _prefix << "start = [" << _machines.size() << "] of {int}  /* nested machines to start at next macrostep */" << std::endl;
	}
	
	stream << "hidden int " << _prefix << "_index;             /* helper for indexless foreach loops */" << std::endl;
	stream << "hidden int " << _prefix << "procid;             /* the process id running this machine */" << std::endl;
	stream << "bool " << _prefix << "spontaneous;              /* whether to take spontaneous transitions */" << std::endl;
	stream << "bool " << _prefix << "done;                     /* is the state machine stopped? */" << std::endl;
	stream << "bool " << _prefix << "canceled;                 /* is the state machine canceled? */" << std::endl;

	if (_analyzer->getTypes().types.find("_ioprocessors") != _analyzer->getTypes().types.end()) {
		stream << "hidden _ioprocessors_t " << _prefix << "_ioprocessors;" << std::endl;
		_varInitializers.push_front("_ioprocessors.scxml.location = " + (_invokerid.size() > 0 ? _analyzer->macroForLiteral(_invokerid) : "1") + ";");
	}
	
	if (_prefix.size() == 0 || _prefix == "MAIN_") {
		if (_analyzer->usesEventField("sendid")) {
			stream << "chan sendIdQ = [" << MAX(_externalQueueLength + 1, 1) << "] of {_event_t}  /* temporary queue to cancel events per sendidexpr */" << std::endl;
			stream << "hidden int _lastSendId = 0;         /* sequential counter for send ids */";
		}

		if (_analyzer->usesEventField("delay")) {
			stream << "hidden int _lastSeqId = 0;          /* sequential counter for delayed events */";
		}
	}
//	if (_analyzer->usesPlatformVars()) {
//		stream << "_x_t _x;" << std::endl;
//	}

	if (_analyzer->usesInPredicate()) {
		stream << "_x_t " << _prefix << "_x;" << std::endl;
	}

	stream << std::endl << std::endl;

	// get all data elements
	NodeSet<std::string> datas = _xpath.evaluate("//" + _nsInfo.xpathPrefix + "data", _scxml).asNodeSet();
	
	// write their text content
	stream << "/* data model variables" << (_prefix.size() > 0 ? " for " + _prefix : "") << " */" << std::endl;
	std::set<std::string> processedIdentifiers;
	
	// automatic types
	PromelaCodeAnalyzer::PromelaTypedef allTypes = _analyzer->getTypes();

	for (int i = 0; i < datas.size(); i++) {
		
		Node<std::string> data = datas[i];
		if (isInEmbeddedDocument(data))
			continue;
		
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
				LOG(ERROR) << "Automatic or no type for '" << identifier << "' but no type resolved";
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

#if 0
		
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
			std::string decl = type + " " + _prefix + identifier + arrSize;
			stream << decl << ";" << std::endl;
			
			if (arrSize.length() > 0) {
				_varInitializers.push_back(value);
			} else {
				if (expression.length() > 0) {
					// id and expr given
					_varInitializers.push_back(identifier + " = " + boost::trim_copy(expression) + ";");
				} else if (value.length() > 0) {
					// id and text content given
					_varInitializers.push_back(identifier + " = " + value + ";");
				}
			}
		} else if (value.length() > 0) {
			// no id but text content given
			stream << beautifyIndentation(value) << std::endl;
		}
#endif
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
		if (typeIter->first == "_event" || typeIter->first == "_ioprocessors" || typeIter->first == "_SESSIONID" || typeIter->first == "_NAME") {
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

void ChartToPromela::writeEventSources(std::ostream& stream) {
	std::list<PromelaInline>::iterator inlineIter;

	if (_globalEventSource) {
		_globalEventSource.writeBody(stream);
	}

	std::map<std::string, PromelaEventSource>::iterator invIter = _invokers.begin();
	while(invIter != _invokers.end()) {
		invIter->second.writeBody(stream);
		invIter++;
	}
}

void ChartToPromela::writeStartInvoker(std::ostream& stream, const Arabica::DOM::Node<std::string>& node, ChartToPromela* invoker, int indent) {
	std::string padding;
	for (int i = 0; i < indent; i++) {
		padding += "  ";
	}

	// set from namelist
	if (HAS_ATTR_CAST(node, "namelist")) {
		std::list<std::string> namelist = tokenize(ATTR_CAST(node, "namelist"));
		for (std::list<std::string>::iterator nlIter = namelist.begin(); nlIter != namelist.end(); nlIter++) {
			if (invoker->_dataModelVars.find(*nlIter) != invoker->_dataModelVars.end()) {
				stream << padding << invoker->_prefix << *nlIter << " = " << _prefix << *nlIter << std::endl;
			}
		}
	}
	
	// set from params
	NodeSet<std::string> invokeParams = filterChildElements(_nsInfo.xmlNSPrefix + "param", node);
	for (int i = 0; i < invokeParams.size(); i++) {
		std::string identifier = ATTR_CAST(invokeParams[i], "name");
		std::string expression = ATTR_CAST(invokeParams[i], "expr");
		if (invoker->_dataModelVars.find(identifier) != invoker->_dataModelVars.end()) {
			stream << padding << invoker->_prefix << identifier << " = " << ADAPT_SRC(expression) << ";" << std::endl;
		}
	}
	
	stream << padding << "run " << invoker->_prefix << "run() priority 20;" << std::endl;
	if (HAS_ATTR_CAST(node, "idlocation")) {
		stream << padding << ADAPT_SRC(ATTR_CAST(node, "idlocation")) << " = " << _analyzer->macroForLiteral(invoker->_invokerid) << ";" << std::endl;
	}

}

void ChartToPromela::writeFSM(std::ostream& stream) {
	NodeSet<std::string> transitions;

	stream << "proctype " << (_prefix.size() == 0 ? "machine_" : _prefix) << "run() {" << std::endl;
	stream << "  " << _prefix << "done = false;" << std::endl;
	stream << "  " << _prefix << "canceled = false;" << std::endl;
	stream << "  " << _prefix << "spontaneous = true;" << std::endl;
	stream << "  " << _prefix << "procid = _pid;" << std::endl;
	// write initial transition
//	transitions = filterChildElements(_nsInfo.xmlNSPrefix + "transition", _startState);
//	assert(transitions.size() == 1);

	stream << std::endl << "/* global scripts */" << std::endl;
	NodeSet<std::string> scripts = filterChildElements(_nsInfo.xmlNSPrefix + "script", _scxml, false);
	for (int i = 0; i < scripts.size(); i++) {
		writeExecutableContent(stream, scripts[i], 1);
	}
	stream << std::endl;

	stream << "/* transition to initial state */" << std::endl;
	assert(_start->sortedOutgoing.size() == 1);
	// initial transition has to be first one for control flow at start
	writeTransition(stream, _start->sortedOutgoing.front(), 1);
	stream << std::endl;
	
	// every other transition
	for (std::map<std::string, GlobalState*>::iterator stateIter = _activeConf.begin(); stateIter != _activeConf.end(); stateIter++) {
		for (std::list<GlobalTransition*>::iterator transIter = stateIter->second->sortedOutgoing.begin(); transIter != stateIter->second->sortedOutgoing.end(); transIter++) {
			// don't write initial transition
			if (_start->sortedOutgoing.front() == *transIter)
				continue;
			// don't write trivial or history transitions
			if ((*transIter)->historyBase == NULL) // TODO!
//				if ((*transIter)->hasExecutableContent && (*transIter)->historyBase == NULL)
				writeTransition(stream, *transIter, 1);
		}
	}

	stream << std::endl;
	stream << _prefix << "macroStep:" << std::endl;
	stream << "  /* push send events to external queue */" << std::endl;
	stream << "  do" << std::endl;
	if (_analyzer->usesEventField("delay")) {
		stream << "  :: len(" << _prefix << "tmpQ) != 0 -> { " << _prefix << "tmpQ?" << _prefix << "_event; " << _prefix << "eQ!!" << _prefix << "_event }" << std::endl;
	} else {
		stream << "  :: len(" << _prefix << "tmpQ) != 0 -> { " << _prefix << "tmpQ?" << _prefix << "_event; " << _prefix << "eQ!" << _prefix << "_event }" << std::endl;
	}
	stream << "  :: else -> break;" << std::endl;
	stream << "  od;" << std::endl << std::endl;

	if (_machines.size() > 0) {
		stream << "  /* start pending invokers */" << std::endl;
		stream << "  int invokerId;" << std::endl;
		stream << "  do" << std::endl;
		stream << "  :: " << _prefix << "start?invokerId -> {" << std::endl;
		stream << "  if " << std::endl;
		for (std::map<Arabica::DOM::Node<std::string>, ChartToPromela*>::iterator machIter = _machines.begin(); machIter != _machines.end(); machIter++) {
			stream << "  :: invokerId == " << _analyzer->macroForLiteral(machIter->second->_invokerid) << " -> {" << std::endl;
			writeStartInvoker(stream, machIter->first, machIter->second, 2);
			stream << "  }" << std::endl;
		}
		stream << "  :: else -> skip; " << std::endl;
		stream << "  fi " << std::endl;
		stream << "  } " << std::endl;
		stream << "  :: else -> break;" << std::endl;
		stream << "  od" << std::endl;
	}
	
	if (_analyzer->usesEventField("delay")) {
		stream << "  /* find machine with next event due */" << std::endl;
		stream << "  if" << std::endl;
		stream << "  :: len(" << _prefix << "iQ) != 0 -> skip;    /* internal queue not empty -> do not reduce our priority */" << std::endl;
		stream << "  :: " << _prefix << "eQ?\? <0> -> skip;           /* at least one event without delay -> do not reduce our priority */" << std::endl;
		stream << "  :: timeout -> { "<< std::endl;
	//	stream << "    /* determine queue with shortest delay in front */" << std::endl;
		stream << "    atomic {" << std::endl;
		stream << "      int nextPid;" << std::endl;
		stream << "      int lowestDelay = 0;" << std::endl;
		stream << "      _event_t tmpE;" << std::endl;

		for (std::map<Arabica::DOM::Node<std::string>, ChartToPromela*>::iterator queueIter = _machinesAll->begin(); queueIter != _machinesAll->end(); queueIter++) {
			std::list<std::string> queues;
			queues.push_back("eQ");
			queues.push_back("tmpQ");
			for (std::list<std::string>::iterator qIter = queues.begin(); qIter != queues.end(); qIter++) {
				stream << "      if" << std::endl;
				stream << "      :: len(" << queueIter->second->_prefix << *qIter << ") > 0 -> {" << std::endl;
				stream << "        " << queueIter->second->_prefix << *qIter << "?<tmpE>;" << std::endl;
				stream << "        if" << std::endl;
				stream << "        :: (tmpE.delay < lowestDelay || lowestDelay == 0) -> {" << std::endl;
				stream << "          lowestDelay = tmpE.delay;" << std::endl;
				stream << "          nextPid = " << queueIter->second->_prefix << "procid;" << std::endl;
				stream << "        }" << std::endl;
				stream << "        :: else -> skip;" << std::endl;
				stream << "        fi;" << std::endl;
				stream << "      }" << std::endl;
				stream << "      :: else -> skip;;" << std::endl;
				stream << "      fi;" << std::endl;
			}
		}
		
		stream << "      set_priority(nextPid, 10);" << std::endl;
		stream << "      if" << std::endl;
		stream << "      :: (nextPid != _pid) -> set_priority(_pid, 1);" << std::endl;
		stream << "      :: else -> skip;" << std::endl;
		stream << "      fi;" << std::endl;
		stream << "    }" << std::endl;
		stream << "  }" << std::endl;
		stream << "  fi;" << std::endl;
		stream << "  set_priority(_pid, 10);" << std::endl << std::endl;
	}
	
	stream << "  /* pop an event */" << std::endl;
	stream << "  if" << std::endl;
	stream << "  :: len(" << _prefix << "iQ) != 0 -> " << _prefix << "iQ ? " << _prefix << "_event   /* from internal queue */" << std::endl;
	stream << "  :: else -> " << _prefix << "eQ ? " << _prefix << "_event           /* from external queue */" << std::endl;
	stream << "  fi;" << std::endl << std::endl;
	
	stream << "  /* terminate if we are stopped */" << std::endl;
	stream << "  if" << std::endl;
	stream << "  :: " << _prefix << "done -> goto " << _prefix << "terminate;" << std::endl;
	if (_parent != NULL) {
		stream << "  :: " << _prefix << "canceled -> goto " << _prefix << "cancel;" << std::endl;
	}
	stream << "  :: else -> skip;" << std::endl;
	stream << "  fi;" << std::endl << std::endl;

#if 1
	{
		bool finalizeFound = false;
		for (std::map<Arabica::DOM::Node<std::string>, ChartToPromela*>::iterator invIter = _machines.begin(); invIter != _machines.end(); invIter++) {
			NodeSet<std::string> finalizes = filterChildElements(_nsInfo.xmlNSPrefix + "finalize", invIter->first, false);
			if (finalizes.size() > 0) {
				finalizeFound = true;
				break;
			}
		}
		if (finalizeFound) {
			stream << "  /* <finalize> event */" << std::endl;
			stream << "  if" << std::endl;
			for (std::map<Arabica::DOM::Node<std::string>, ChartToPromela*>::iterator invIter = _machines.begin(); invIter != _machines.end(); invIter++) {
				NodeSet<std::string> finalizes = filterChildElements(_nsInfo.xmlNSPrefix + "finalize", invIter->first, false);
				if (finalizes.size() > 0) {
					stream << "  :: " << _prefix << "_event.invokeid == " << _analyzer->macroForLiteral(invIter->second->_invokerid) << " -> {" << std::endl;
					writeExecutableContent(stream, finalizes[0], 2);
					stream << "  } " << std::endl;
				}
			}
			stream << "  :: else -> skip;" << std::endl;
			stream << "  fi;" << std::endl << std::endl;
		}
	}
#endif
	
	stream << "  /* autoforward to respective invokers */" << std::endl;
	for (std::map<Arabica::DOM::Node<std::string>, ChartToPromela*>::iterator invIter = _machines.begin(); invIter != _machines.end(); invIter++) {
		if (invIter->second == this) {
			continue;
		}
		//std::cout << invIter->first << std::endl;
		if (DOMUtils::attributeIsTrue(ATTR_CAST(invIter->first, "autoforward"))) {
			stream << "  if" << std::endl;
			stream << "  :: " << invIter->second->_prefix << "done -> skip;" << std::endl;
			stream << "  :: " << invIter->second->_prefix << "canceled -> skip;" << std::endl;
			stream << "  :: else -> { " << invIter->second->_prefix << "eQ!!" << _prefix << "_event" << " }" << std::endl;
			stream << "  fi;" << std::endl << std::endl;

		}
	}
	stream << std::endl;
	
	
	stream << _prefix << "microStep:" << std::endl;
	stream << "  /* event dispatching per state */" << std::endl;
	stream << "  if" << std::endl;

	writeEventDispatching(stream);

	stream << "/* this is an error as we dispatched all valid states */" << std::endl;
	stream << "  :: else -> assert(false);" << std::endl;
	stream << "  fi;" << std::endl;
	stream << std::endl;
	stream << _prefix << "terminate: skip;" << std::endl;

	if (_parent != NULL) {
		stream << "  {" << std::endl;
		stream << "    _event_t tmpE;" << std::endl;
		stream << "    tmpE.name = " << _analyzer->macroForLiteral("done.invoke." + _invokerid) << ";" << std::endl;
		if (_invokerid.length() > 0) {
			stream << "    tmpE.invokeid = " << _analyzer->macroForLiteral(_invokerid) << ";" << std::endl;
		}
		if (_analyzer->usesEventField("delay")) {
			stream << "    _lastSeqId = _lastSeqId + 1;" << std::endl;
			stream << "    tmpE.seqNr = _lastSeqId;" << std::endl;
			stream << "    " << _parent->_prefix << "eQ!!tmpE;" << std::endl;
		} else {
			stream << "    " << _parent->_prefix << "eQ!tmpE;" << std::endl;
		}
		stream << "  }" << std::endl;
		stream << _prefix << "cancel: skip;" << std::endl;
		writeRemovePendingEventsFromInvoker(stream, this, 1, true);

	}
	
	// stop all event sources
	if (_globalEventSource)
		_globalEventSource.writeStop(stream, 1);

	std::map<std::string, PromelaEventSource>::iterator invIter = _invokers.begin();
	while(invIter != _invokers.end()) {
		invIter->second.writeStop(stream, 1);
		invIter++;
	}

	stream << "}" << std::endl;
}

void ChartToPromela::writeRemovePendingEventsFromInvoker(std::ostream& stream, ChartToPromela* invoker, int indent, bool atomic) {
	std::string padding;
	for (int i = 0; i < indent; i++) {
		padding += "  ";
	}

	if (!invoker || !invoker->_parent)
		return;
	
	if (_analyzer->usesEventField("delay")) {
		if (atomic) {
			stream << padding << "atomic {" << std::endl;
		} else {
			stream << padding << "{" << std::endl;
		}
		stream << padding << "  /* remove all this invoker's pending events from all queues */" << std::endl;
		stream << padding << "  _event_t tmpE;" << std::endl;
		std::list<ChartToPromela*> others;
		others.push_back(invoker->_parent);
		for (std::map<Arabica::DOM::Node<std::string>, ChartToPromela*>::iterator queueIter = invoker->_parent->_machines.begin(); queueIter != invoker->_parent->_machines.end(); queueIter++) {
			if (queueIter->second != invoker)
				others.push_back(queueIter->second);
		}
		
		for (std::list<ChartToPromela*>::iterator queueIter = others.begin(); queueIter != others.end(); queueIter++) {
			stream << padding << "  do" << std::endl;
			stream << padding << "  :: (len(" << (*queueIter)->_prefix << "eQ) > 0) -> { " << (*queueIter)->_prefix << "eQ?tmpE; " << _prefix << "tmpQ!tmpE;  }" << std::endl;
			stream << padding << "  :: else -> break;" << std::endl;
			stream << padding << "  od" << std::endl;

			stream << padding << "  do" << std::endl;
			stream << padding << "  :: (len(" << _prefix << "tmpQ) > 0) -> {" << std::endl;
			stream << padding << "    " << _prefix << "tmpQ?tmpE;" << std::endl;
			stream << padding << "    if" << std::endl;
			stream << padding << "    :: (tmpE.invokeid != " << _analyzer->macroForLiteral(invoker->_invokerid) << " || tmpE.delay == 0) -> " << (*queueIter)->_prefix << "eQ!tmpE" << std::endl;
			stream << padding << "    :: else -> skip;" << std::endl;
			stream << padding << "    fi" << std::endl;
			stream << padding << "  }" << std::endl;
			stream << padding << "  :: else -> break;" << std::endl;
			stream << padding << "  od" << std::endl;

		}
		stream << padding << "}" << std::endl;
	}

}

void ChartToPromela::writeEventDispatching(std::ostream& stream) {
	for (std::map<std::string, GlobalState*>::iterator stateIter = _activeConf.begin(); stateIter != _activeConf.end(); stateIter++) {
//		if (_globalStates[i] == _startState)
//			continue;

		// do not write state with history - we only iterate pure active
//		if (stateIter->second->historyStatesRefs.size() > 0)
//			continue;
		
		const std::string& stateId = stateIter->first;
		const GlobalState* state = stateIter->second;
		
		stream << std::endl << "/* ### current state ";
		FlatStateIdentifier flatActiveSource(stateId);
		PRETTY_PRINT_LIST(stream, flatActiveSource.getActive());
		stream << " ######################## */" << std::endl;

		stream << "  :: (" << _prefix << "s == s" << state->activeIndex << ") -> {" << std::endl;

		writeDispatchingBlock(stream, state->sortedOutgoing, 2);
//		stream << "    goto macroStep;";
		stream << "  }" << std::endl;
	}
}
	
void ChartToPromela::writeDispatchingBlock(std::ostream& stream, std::list<GlobalTransition*> transitions, int indent) {
	std::string padding;
	for (int i = 0; i < indent; i++) {
		padding += "  ";
	}

	if (transitions.size() == 0) {
		stream << "/* no transition applicable */" << std::endl;
		stream << padding << _prefix << "spontaneous = false;" << std::endl;
		stream << padding << "goto " << _prefix << "macroStep;" << std::endl;
		return;
	}


	GlobalTransition* currTrans = transitions.front();
	transitions.pop_front();

	stream << padding << "if" << std::endl;

	if (currTrans->condition.size() > 0) {
		stream << padding << ":: ((";
	} else {
		stream << padding << ":: (";
	}

	if (currTrans->isEventless) {
		stream << _prefix << "spontaneous";
	} else {
		std::string eventDescs = currTrans->eventDesc;
		
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
				std::set<std::string> tmp = _analyzer->getEventsWithPrefix(*eventNameIter);
				eventPrefixes.insert(tmp.begin(), tmp.end());
			}
			eventNameIter++;
		}

		if (eventPrefixes.size() > 0) {
			stream << "!" << _prefix << "spontaneous";
		} else {
			stream << "!" << _prefix << "spontaneous";
		}

		if (eventPrefixes.size() > 0)
			stream << " &&";

		if (eventPrefixes.size() > 1)
			stream << " (";
		
		std::string seperator;
		std::set<std::string>::iterator eventIter = eventPrefixes.begin();
		while(eventIter != eventPrefixes.end()) {
			if (_analyzer->usesComplexEventStruct()) {
				stream << seperator << " " << _prefix << "_event.name == " << _analyzer->macroForLiteral(*eventIter);
			} else {
				stream << seperator << " " << _prefix << "_event == " << _analyzer->macroForLiteral(*eventIter);
			}
			seperator = " || ";
			eventIter++;
		}

		if (eventPrefixes.size() > 1)
			stream << ")";

	}

	stream << ")";
	if (currTrans->condition.size() > 0) {
		stream << " && (" + ADAPT_SRC(currTrans->condition) + "))";
	}
	if (currTrans->hasExecutableContent || currTrans->historyTrans.size() > 0) {
		stream << " -> { " << std::endl;

		stream << "/* transition to ";
		FlatStateIdentifier flatActiveSource(currTrans->activeDestination);
		PRETTY_PRINT_LIST(stream, flatActiveSource.getActive());
		stream << " */" << std::endl;
		
		stream << padding << "  goto " << _prefix << "t" << currTrans->index << ";" << std::endl;
		stream << padding << "}" << std::endl;

	} else {
		
		stream << " -> {" << std::endl;
		GlobalState* newState = _activeConf[currTrans->activeDestination];
		assert(newState != NULL);

		stream << "/* new state ";
		FlatStateIdentifier flatActiveDest(currTrans->activeDestination);
		PRETTY_PRINT_LIST(stream, flatActiveDest.getActive());
		stream <<  " */" << std::endl;

		stream << padding << "  " << _prefix << "s = s" << newState->activeIndex << ";" << std::endl;

		writeTransitionClosure(stream, currTrans, newState, indent + 1);
		stream << padding << "}" << std::endl;
	}

	stream << padding << ":: else -> {" << std::endl;

	writeDispatchingBlock(stream, transitions, indent + 1);

	stream << padding << "}" << std::endl;
	stream << padding << "fi;" << std::endl;
}

void ChartToPromela::writeMain(std::ostream& stream) {
	stream << std::endl;
	stream << "init {" << std::endl;
	if (_varInitializers.size() > 0) {
		stream << "/* initialize data model variables */" << std::endl;
		std::list<std::string>::iterator initIter = _varInitializers.begin();
		while(initIter != _varInitializers.end()) {
			stream << ADAPT_SRC(beautifyIndentation(*initIter, 1)) << std::endl;
			initIter++;
		}
		stream << std::endl;
	}
	if (_globalEventSource)
		_globalEventSource.writeStart(stream, 1);
	stream << "  run " << (_prefix.size() == 0 ? "machine_" : _prefix) << "run() priority 10;" << std::endl;
	stream << "}" << std::endl;

}


void ChartToPromela::initNodes() {
	// some things we share with our invokers
	if (_analyzer == NULL)
		_analyzer = new PromelaCodeAnalyzer();
	
	if (_machinesAll == NULL) {
		_machinesAll = new std::map<Arabica::DOM::Node<std::string>, ChartToPromela*>();
		(*_machinesAll)[_scxml] = this;
	}
	
	if (_machinesAllPerId == NULL)
		_machinesAllPerId = new std::map<std::string, Arabica::DOM::Node<std::string> >();

	if (_parentTopMost == NULL)
		_parentTopMost = this;
	
	_internalQueueLength = getMinInternalQueueLength(MSG_QUEUE_LENGTH);
	_externalQueueLength = getMinExternalQueueLength(MSG_QUEUE_LENGTH);

	// get all states
	NodeSet<std::string> states = getAllStates();
	for (int i = 0; i < states.size(); i++) {
		if (InterpreterImpl::isInEmbeddedDocument(states[i]))
			continue;
		Element<std::string> stateElem(states[i]);
		_analyzer->addOrigState(ATTR(stateElem, "id"));
		if (isCompound(stateElem) || isParallel(stateElem)) {
			_analyzer->addEvent("done.state." + ATTR(stateElem, "id"));
		}
	}
	
	{
		// shorten UUID ids at invokers for readability
		NodeSet<std::string> invokes = filterChildElements(_nsInfo.xmlNSPrefix + "invoke", _scxml, true);
		invokes.push_back(filterChildElements(_nsInfo.xmlNSPrefix + "uninvoke", _scxml, true));

		// make sure all invokers have an id!
		for (int i = 0; i < invokes.size(); i++) {
			if (!HAS_ATTR_CAST(invokes[i], "id")) {
				Element<std::string> invokeElem(invokes[i]);
				invokeElem.setAttribute("id", "INV_" + UUID::getUUID().substr(0,5));
			} else if (HAS_ATTR_CAST(invokes[i], "id") && UUID::isUUID(ATTR_CAST(invokes[i], "id"))) {
				// shorten UUIDs
				Element<std::string> invokeElem(invokes[i]);
				invokeElem.setAttribute("id", "INV_" + ATTR_CAST(invokes[i], "id").substr(0,5));
			}
		}

	}
	
	// are there nestes SCXML invokers?
	{
		NodeSet<std::string> invokes = filterChildElements(_nsInfo.xmlNSPrefix + "invoke", _scxml, true);
		for (int i = 0; i < invokes.size(); i++) {
			if (!HAS_ATTR_CAST(invokes[i], "type") ||
					ATTR_CAST(invokes[i], "type") == "scxml" ||
					ATTR_CAST(invokes[i], "type") == "http://www.w3.org/TR/scxml/#SCXMLEventProcessor" ||
					ATTR_CAST(invokes[i], "type") == "http://www.w3.org/TR/scxml/") {
				assert(HAS_ATTR_CAST(invokes[i], "id"));
				Element<std::string>(invokes[i]).setAttribute("name", ATTR_CAST(invokes[i], "id"));
				
				_prefix = "MAIN_";
				Interpreter nested;
				if (HAS_ATTR_CAST(invokes[i], "src")) {
					URL absUrl(ATTR_CAST(invokes[i], "src"));
					absUrl.toAbsolute(_baseURL[_scxml]);
					nested = Interpreter::fromURL(absUrl);

				} else {
					NodeSet<std::string> nestedContent = InterpreterImpl::filterChildElements(_nsInfo.xmlNSPrefix + "content", invokes[i]);
					assert(nestedContent.size() == 1);
					NodeSet<std::string> nestedRoot = InterpreterImpl::filterChildElements(_nsInfo.xmlNSPrefix + "scxml", nestedContent[0]);
					assert(nestedRoot.size() == 1);

					DOMImplementation<std::string> domFactory = Arabica::SimpleDOM::DOMImplementation<std::string>::getDOMImplementation();
					Document<std::string> nestedDoc = domFactory.createDocument(_scxml.getOwnerDocument().getNamespaceURI(), "", 0);
					Node<std::string> importRoot = nestedDoc.importNode(nestedRoot[0], true);
					nestedDoc.appendChild(importRoot);
					
					nested = Interpreter::fromDOM(nestedDoc, _nsInfo, _sourceURL);
				}
				
//				std::cout << invokes[i] << std::endl;
				
				// we found machines but have no prefix
				if (_prefix.length() == 0)
					_prefix = "MAIN_";

				_machines[invokes[i]] = new ChartToPromela(nested);
				_machines[invokes[i]]->_analyzer = _analyzer;
				_machines[invokes[i]]->_parent = this;
				_machines[invokes[i]]->_parentTopMost = _parentTopMost;
				_machines[invokes[i]]->_machinesAll = _machinesAll;
				(*_machinesAll)[invokes[i]] = _machines[invokes[i]];
				
				_machines[invokes[i]]->_invokerid = ATTR_CAST(invokes[i], "id");
				_machines[invokes[i]]->_prefix = ATTR_CAST(invokes[i], "id") + "_";
				
				_analyzer->addLiteral(_machines[invokes[i]]->_invokerid);
				_analyzer->addEvent("done.invoke." + _machines[invokes[i]]->_invokerid);
				
				_machinesPerId[ATTR_CAST(invokes[i], "id")] = invokes[i];
				(*_machinesAllPerId)[ATTR_CAST(invokes[i], "id")] = invokes[i];
			}
		}
	}

	if (_machines.size() > 0) {
		_analyzer->addCode("_event.invokeid", this);
	}
	
	// gather all potential members per history
	std::map<std::string, Arabica::DOM::Element<std::string> >::iterator histIter = _historyTargets.begin();
	while(histIter != _historyTargets.end()) {
		NodeSet<std::string> histStatesMembers;
		bool isDeep = (HAS_ATTR_CAST(histIter->second, "type") && ATTR_CAST(histIter->second, "type") == "deep");
		histStatesMembers.push_back(filterChildElements(_nsInfo.xmlNSPrefix + "state", histIter->second.getParentNode(), isDeep));
		histStatesMembers.push_back(filterChildElements(_nsInfo.xmlNSPrefix + "parallel", histIter->second.getParentNode(), isDeep));
		histStatesMembers.push_back(filterChildElements(_nsInfo.xmlNSPrefix + "final", histIter->second.getParentNode(), isDeep));

		for (int i = 0; i < histStatesMembers.size(); i++) {
			_historyMembers[histIter->first].insert(std::make_pair(ATTR_CAST(histStatesMembers[i], "id"), i));
		}
		histIter++;
	}
	
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
					_analyzer->addEvent(eventName);
			}
		}
	}

	// transform data / assign json into PROMELA statements
	{
		NodeSet<std::string> asgn;
		asgn.push_back(filterChildElements(_nsInfo.xmlNSPrefix + "data", _scxml, true));
		asgn.push_back(filterChildElements(_nsInfo.xmlNSPrefix + "assign", _scxml, true));

		for (int i = 0; i < asgn.size(); i++) {
			if (isInEmbeddedDocument(asgn[i]))
				continue;
			
			Element<std::string> asgnElem(asgn[i]);
			
			std::string key;
			if (HAS_ATTR(asgnElem, "id")) {
				key = ATTR(asgnElem, "id");
			} else if (HAS_ATTR(asgnElem, "location")) {
				key = ATTR(asgnElem, "location");
			}
			
			if (key.length() == 0)
				continue;
			
			std::string value;
			if (HAS_ATTR(asgnElem, "expr")) {
				value = ATTR(asgnElem, "expr");
			} else if (HAS_ATTR(asgnElem, "src")) {
				URL absUrl(ATTR_CAST(asgnElem, "src"));
				absUrl.toAbsolute(_baseURL[_scxml]);
				value = absUrl.getInContent();
			} else {
				NodeSet<std::string> textChilds = filterChildType(Node_base::TEXT_NODE, asgnElem);
				if (textChilds.size() > 0) {
					for (int j = 0; j < textChilds.size(); j++) {
						value += textChilds[j].getNodeValue();
					}
				}
			}
			
			boost::trim(value);
			if (value.size() == 0)
				continue;
			
			// remove all children, we will replae by suitable promela statements
			while(asgnElem.hasChildNodes())
				asgnElem.removeChild(asgnElem.getFirstChild());
			
			std::string newValue;
			Data json = Data::fromJSON(value);
			if (!json.empty()) {
				newValue = dataToAssignments(key, json);
			} else {
				newValue = key + " = " + value + ";";
			}
			newValue = sanitizeCode(newValue);
			_analyzer->addCode(newValue, this);
			
			if (asgnElem.getLocalName() == "data")
				_varInitializers.push_back(newValue);
			Text<std::string> newText = _document.createTextNode(newValue);
			asgnElem.insertBefore(newText, Node<std::string>());
		}
	}
	
	// do we need sendid / invokeid?
	{
		NodeSet<std::string> invokes = filterChildElements(_nsInfo.xmlNSPrefix + "invoke", _scxml, true);
		NodeSet<std::string> sends = filterChildElements(_nsInfo.xmlNSPrefix + "send", _scxml, true);
		
		for (int i = 0; i < sends.size(); i++) {
			if (HAS_ATTR_CAST(sends[i], "idlocation")) {
				_analyzer->addCode("_event.sendid", this);
			}
			if (HAS_ATTR_CAST(sends[i], "id")) {
				_analyzer->addLiteral(ATTR_CAST(sends[i], "id"));
				_analyzer->addCode("_event.sendid", this);
			}
		}

		// do we need delays?
		for (int i = 0; i < sends.size(); i++) {
			if (HAS_ATTR_CAST(sends[i], "delay") || HAS_ATTR_CAST(sends[i], "delayexpr")) {
				_analyzer->addCode("_event.delay", this);
				_analyzer->addCode("_event.seqNr", this);
			}
		}
	}
	
	{
		// string literals for raise / send content
		NodeSet<std::string> withContent;
		withContent.push_back(filterChildElements(_nsInfo.xmlNSPrefix + "send", _scxml, true));
		withContent.push_back(filterChildElements(_nsInfo.xmlNSPrefix + "raise", _scxml, true));

		for (int i = 0; i < withContent.size(); i++) {
			NodeSet<std::string> content = filterChildElements(_nsInfo.xmlNSPrefix + "content", withContent[i], true);
			for (int j = 0; j < content.size(); j++) {
				Element<std::string> contentElem(content[j]);
				std::string content = spaceNormalize(contentElem.getFirstChild().getNodeValue());
				if (!isNumeric(content.c_str(), 10))
					_analyzer->addLiteral(content);
			}
		}
	}
	// external event names from comments and event sources
	NodeSet<std::string> promelaEventSourceComments;
	NodeSet<std::string> invokers = _xpath.evaluate("//" + _nsInfo.xpathPrefix + "invoke", _scxml).asNodeSet();
	promelaEventSourceComments.push_back(filterChildType(Node_base::COMMENT_NODE, invokers, false)); // comments in invoke elements
	promelaEventSourceComments.push_back(filterChildType(Node_base::COMMENT_NODE, _scxml, false)); // comments in scxml element

	for (int i = 0; i < promelaEventSourceComments.size(); i++) {
		PromelaInlines promInls = PromelaInlines::fromNode(promelaEventSourceComments[i]);
		
		for (	std::list<PromelaInline>::iterator promIter = promInls.code.begin(); promIter != promInls.code.end(); promIter++) {
			if (promIter->type == PromelaInline::PROMELA_EVENT_SOURCE || promIter->type == PromelaInline::PROMELA_EVENT_SOURCE_CUSTOM) {
				PromelaEventSource promES(*promIter, _analyzer, _externalQueueLength);
				if (TAGNAME_CAST(promelaEventSourceComments[i].getParentNode()) == "scxml") {
					promES.type = PromelaEventSource::PROMELA_EVENT_SOURCE_GLOBAL;
					promES.name = "global";
					_globalEventSource = promES;
				} else {
					Element<std::string> invoker = Element<std::string>(promelaEventSourceComments[i].getParentNode());
					if (!HAS_ATTR_CAST(promelaEventSourceComments[i].getParentNode(), "id")) {
						invoker.setAttribute("invokeid", "invoker" + toStr(_invokers.size())); // if there is no invokeid, enumerate
					} else {
						invoker.setAttribute("invokeid", ATTR_CAST(promelaEventSourceComments[i].getParentNode(), "id"));
					}
					std::string invokeId = ATTR_CAST(promelaEventSourceComments[i].getParentNode(), "invokeid");

					promES.type = PromelaEventSource::PROMELA_EVENT_SOURCE_INVOKER;
					promES.name = invokeId;
					_invokers[invokeId] = promES;
				}
			}
		}
	}
	
	// add platform variables as string literals
	_analyzer->addLiteral(_prefix + "_sessionid");
	_analyzer->addLiteral(_prefix + "_name");

	if (HAS_ATTR(_scxml, "name")) {
		_analyzer->addLiteral(ATTR(_scxml, "name"), _analyzer->indexForLiteral(_prefix + "_sessionid"));
	}

	NodeSet<std::string> contents = filterChildElements(_nsInfo.xmlNSPrefix + "content", _scxml, true);
	for (int i = 0; i < contents.size(); i++) {
		Element<std::string> contentElem = Element<std::string>(contents[i]);
		if (contentElem.hasChildNodes() && contentElem.getFirstChild().getNodeType() == Node_base::TEXT_NODE && contentElem.getChildNodes().getLength() == 1) {
			std::string content = contentElem.getFirstChild().getNodeValue();
			_analyzer->addLiteral(spaceNormalize(content));
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
//		withText.push_back(filterChildElements(_nsInfo.xmlNSPrefix + "data", _scxml, true));
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
	{
		NodeSet<std::string> foreachs = filterChildElements(_nsInfo.xmlNSPrefix + "foreach", _scxml, true);
		for (int i = 0; i < foreachs.size(); i++) {
			if (HAS_ATTR_CAST(foreachs[i], "index")) {
				allCode.insert(ATTR_CAST(foreachs[i], "index"));
			}
			if (HAS_ATTR_CAST(foreachs[i], "item")) {
				allCode.insert(ATTR_CAST(foreachs[i], "item"));
			}
		}
	}
	for (std::set<std::string>::const_iterator codeIter = allCode.begin(); codeIter != allCode.end(); codeIter++) {
		_analyzer->addCode(*codeIter, this);
	}

	// add all namelist entries to the _event structure
	{
		NodeSet<std::string> withNamelist;
		withNamelist.push_back(filterChildElements(_nsInfo.xmlNSPrefix + "send", _scxml, true));
		withNamelist.push_back(filterChildElements(_nsInfo.xmlNSPrefix + "invoke", _scxml, true));
		for (int i = 0; i < withNamelist.size(); i++) {
			if (HAS_ATTR_CAST(withNamelist[i], "namelist")) {
				std::string namelist = ATTR_CAST(withNamelist[i], "namelist");
				std::list<std::string> names = tokenizeIdRefs(namelist);
				for (std::list<std::string>::iterator nameIter = names.begin(); nameIter != names.end(); nameIter++) {
					_analyzer->addCode("_event.data." + *nameIter + " = 0;", this); // introduce for _event_t typedef
				}
			}
		}
	}
}

	
std::string ChartToPromela::dataToAssignments(const std::string& prefix, const Data& data) {
	std::stringstream retVal;
	if (data.atom.size() > 0) {
		retVal << prefix << " = " << data.atom << ";" << std::endl;
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

void PromelaInline::dump() {
//	std::list<std::list<std::string> >::iterator outerIter = sequences.begin();
//	while(outerIter != sequences.end()) {
//		std::list<std::string>::iterator innerIter = outerIter->begin();
//		while(innerIter != outerIter->end()) {
//			std::cout << *innerIter << " ";
//			innerIter++;
//		}
//		std::cout << std::endl;
//		outerIter++;
//	}
}

void ChartToPromela::writeProgram(std::ostream& stream) {

	if (!HAS_ATTR(_scxml, "datamodel") || ATTR(_scxml, "datamodel") != "promela") {
		LOG(ERROR) << "Can only convert SCXML documents with \"promela\" datamodel";
		return;
	}

	if (_start == NULL) {
		interpret();
	}

	if (HAS_ATTR(_scxml, "binding") && ATTR(_scxml, "binding") != "early") {
		LOG(ERROR) << "Can only convert for early data bindings";
		return;
	}

//	std::cerr << _scxml << std::endl;

	stream << "/* " << _sourceURL.asString() << " */" << std::endl;
	stream << std::endl;

	initNodes();

	for (std::map<Arabica::DOM::Node<std::string>, ChartToPromela*>::iterator nestedIter = _machines.begin(); nestedIter != _machines.end(); nestedIter++) {
		if (nestedIter->second->_start == NULL) {
			nestedIter->second->interpret();
		}
		nestedIter->second->initNodes();
	}

	writeEvents(stream);
	stream << std::endl;
	writeStates(stream);
	stream << std::endl;
	if (_analyzer->usesInPredicate()) {
		writeStateMap(stream);
		stream << std::endl;
	}
	if (_historyMembers.size() > 0) {
		writeHistoryArrays(stream);
		stream << std::endl;
	}
	writeTypeDefs(stream);
	stream << std::endl;
	writeStrings(stream);
	stream << std::endl;
	writeDeclarations(stream);
	
	for (std::map<Arabica::DOM::Node<std::string>, ChartToPromela*>::iterator nestedIter = _machines.begin(); nestedIter != _machines.end(); nestedIter++) {
		nestedIter->second->writeDeclarations(stream);
		stream << std::endl;
	}

	stream << std::endl;
	writeEventSources(stream);
	stream << std::endl;
	writeFSM(stream);
	stream << std::endl;
	writeMain(stream);
	stream << std::endl;

	for (std::map<Arabica::DOM::Node<std::string>, ChartToPromela*>::iterator nestedIter = _machines.begin(); nestedIter != _machines.end(); nestedIter++) {
		nestedIter->second->writeFSM(stream);
		stream << std::endl;
	}

	// write ltl expression for success
	std::stringstream acceptingStates;
	std::string seperator;
	
	for (std::map<std::string, GlobalState*>::iterator stateIter = _activeConf.begin(); stateIter != _activeConf.end(); stateIter++) {
		FlatStateIdentifier flatId(stateIter->first);
		if (std::find(flatId.getActive().begin(), flatId.getActive().end(), "pass") != flatId.getActive().end()) {
			acceptingStates << seperator << _prefix << "s == s" << stateIter->second->activeIndex;
			seperator = " || ";
		}
	}
	if (acceptingStates.str().size() > 0) {
		stream << "ltl { eventually (" << acceptingStates.str() << ") }" << std::endl;
	}
}

}