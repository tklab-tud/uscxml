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

#define NEW_DELAY_RESHUFFLE 1

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

#define TRANSITION_TRACE(transList, value) \
if (_traceTransitions) { \
for (std::set<int>::iterator transRefIter = transList->transitionRefs.begin(); \
     transRefIter != transList->transitionRefs.end(); \
     transRefIter++) { \
        stream << padding << _prefix << "transitions[" << *transRefIter << "] = "#value"; " << std::endl; \
    } \
} \


#define DUMP_STATS(disregardTime) \
uint64_t now = tthread::chrono::system_clock::now(); \
if (now - _lastTimeStamp > 1000 || disregardTime) { \
	std::cerr << "## State     : " << _perfStatesTotal << " [" << _perfStatesProcessed << "/sec]" << std::endl; \
	std::cerr << "## Transition: " << _perfTransTotal << " [" << _perfHistoryProcessed << "/sec]" << std::endl; \
	std::cerr << "## History   : " << _perfHistoryTotal << " [" << _perfHistoryProcessed << "/sec]" << std::endl; \
	std::cerr << "toPML: "; \
	std::cerr << _perfStatesTotal << ", " << _perfStatesProcessed << ", "; \
	std::cerr << _perfTransTotal << ", " << _perfTransProcessed << ", "; \
	std::cerr << _perfHistoryTotal << ", " << _perfHistoryProcessed; \
	std::cerr << std::endl << std::endl; \
	_perfTransProcessed = 0; \
	_perfHistoryProcessed = 0; \
	_perfStatesProcessed = 0; \
	if (!disregardTime)\
		_lastTimeStamp = now; \
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

std::string PromelaCodeAnalyzer::getTypeReset(const std::string& var, const PromelaTypedef& type, const std::string padding) {
    std::stringstream assignment;
    
    std::map<std::string, PromelaTypedef>::const_iterator typeIter = type.types.begin();
    while(typeIter != type.types.end()) {
        const PromelaTypedef& innerType = typeIter->second;
        if (innerType.arraySize > 0) {
            for (int i = 0; i < innerType.arraySize; i++) {
                assignment << padding << var << "." << typeIter->first << "[" << i << "] = 0;" << std::endl;
            }
        } else if (innerType.types.size() > 0) {
            assignment << getTypeReset(var + "." + typeIter->first, typeIter->second, padding);
        } else {
            assignment << padding << var << "." << typeIter->first << " = 0;" << std::endl;
        }
        typeIter++;
    }
    return assignment.str();

}

std::string PromelaCodeAnalyzer::getTypeAssignment(const std::string& varTo, const std::string& varFrom, const PromelaTypedef& type, const std::string padding) {
    std::stringstream assignment;
    
    std::map<std::string, PromelaTypedef>::const_iterator typeIter = type.types.begin();
    while(typeIter != type.types.end()) {
        const PromelaTypedef& innerType = typeIter->second;
        if (innerType.arraySize > 0) {
            for (int i = 0; i < innerType.arraySize; i++) {
                assignment << padding << varTo << "." << typeIter->first << "[" << i << "] = " << varFrom << "." << typeIter->first << "[" << i << "];" << std::endl;
            }
        } else if (innerType.types.size() > 0) {
            assignment << getTypeAssignment(varTo + "." + typeIter->first, varFrom + "." + typeIter->first, typeIter->second, padding);
        } else {
            assignment << padding << varTo << "." << typeIter->first << " = " << varFrom << "." << typeIter->first << ";" << std::endl;
        }
        typeIter++;
    }
    return assignment.str();
}

std::string PromelaCodeAnalyzer::macroForLiteral(const std::string& literal) {
	if (boost::starts_with(literal, "'"))
		throw std::runtime_error("Literal " + literal + " passed with quotes");

	if (_strMacroNames.find(literal) == _strMacroNames.end())
		throw std::runtime_error("No macro for literal '" + literal + "' known");
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
		posList.insert(posList.end(), tmp.begin(), tmp.end());
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
	stream << "/* original state names */" << std::endl;
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
	std::map<std::string, std::map<std::string, size_t> >::iterator histNameIter = _historyMembers.begin();
	while(histNameIter != _historyMembers.end()) {
		stream << "/* history assignments for " << histNameIter->first << std::endl;
		std::map<std::string, size_t>::iterator histMemberIter = histNameIter->second.begin();
		while(histMemberIter != histNameIter->second.end()) {
			stream << "   " << histMemberIter->second << ": " << histMemberIter->first << std::endl;;
			histMemberIter++;
		}
		stream << "*/" << std::endl;
		stream << "bool " << _prefix << "_hist_" << boost::replace_all_copy(boost::to_lower_copy(histNameIter->first), ".", "_") << "[" << histNameIter->second.size() << "];" << std::endl;

		histNameIter++;
	}
}
	
void ChartToPromela::writeTypeDefs(std::ostream& stream) {
	stream << "/* type definitions */" << std::endl;
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
#if NEW_DELAY_RESHUFFLE
#else
                stream << "  int seqNr;" << std::endl;
#endif
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
				condition << itemSep << _prefix << "_hist_" << boost::to_lower_copy(_analyzer->macroForLiteral(relevanthistIter->first)) << "[" << _historyMembers[relevanthistIter->first][*histItemIter] << "]";
				itemSep = " && ";
				histItemIter++;
			}
			relevanthistIter++;
		}

		if (relevantHist.size() > 0)
			memberSep = " || ";

	}
	if (condition.str().size() > 0) {
		return "(" + condition.str() + ")";
	} else {
		assert(false);
	}
	return "true";
}

//std::list<GlobalTransition::Action> ChartToPromela::getTransientContent(GlobalTransition* transition) {
//	std::list<GlobalTransition::Action> content;
//	GlobalTransition* currTrans = transition;
//	for (;;) {
//		if (!HAS_ATTR(currState, "transient") || !DOMUtils::attributeIsTrue(ATTR(currState, "transient")))
//			break;
//		content.push_back(filterChildElements(_nsInfo.xmlNSPrefix + "invoke", currState));
//		content.push_back(filterChildElements(_nsInfo.xmlNSPrefix + "onentry", currState));
//		content.push_back(filterChildElements(_nsInfo.xmlNSPrefix + "onexit", currState));
//		NodeSet<std::string> transitions = filterChildElements(_nsInfo.xmlNSPrefix + "transition", currState);
//		currState = _globalConf[ATTR_CAST(transitions[0], "target")];
//	}
//	
//	return content;
//}

void ChartToPromela::writeTransition(std::ostream& stream, GlobalTransition* transition, int indent) {
	std::string padding;
	for (int i = 0; i < indent; i++) {
		padding += "  ";
	}
	std::list<GlobalTransition*>::const_iterator histIter;
	
    if (envVarIsTrue("USCXML_ANNOTATE_NOCOMMENT")) {
        stream << std::endl << _prefix << "t" << transition->index << ": /* ######################## */ " << std::endl;

    } else {

        stream << std::endl << _prefix << "t" << transition->index << ": /* ######################## " << std::endl;
        FlatStateIdentifier flatActiveSource(transition->source);
        stream << "     from state: ";
        PRETTY_PRINT_LIST(stream, flatActiveSource.getActive());
        stream << std::endl;
    //	stream << "   with history: " << flatActiveSource.getFlatHistory() << std::endl;
        stream << " ----- on event: " << (transition->eventDesc.size() > 0 ? transition->eventDesc : "SPONTANEOUS") << " --" << std::endl;
        stream << "       to state: ";
        std::set<FlatStateIdentifier> destinations;
        destinations.insert(FlatStateIdentifier(transition->destination));
        histIter = transition->historyTrans.begin();
        while(histIter != transition->historyTrans.end()) {
            destinations.insert(FlatStateIdentifier((*histIter)->destination));
            histIter++;
        }
        std::string seperator = "";
        for (std::set<FlatStateIdentifier>::iterator destIter = destinations.begin(); destIter != destinations.end(); destIter++) {
            stream << seperator;
            PRETTY_PRINT_LIST(stream, destIter->getActive());
            stream << " with " << (destIter->getFlatHistory().size() > 0 ? destIter->getFlatHistory() : "no history");
            seperator = "\n                 ";
        }
        stream << std::endl;

        stream << "############################### */" << std::endl;
    }
    stream << std::endl;
	stream << padding << "skip;" << std::endl;
	stream << padding << "d_step {" << std::endl;
	if (_writeTransitionPrintfs)
		stream << padding << "  printf(\"Taking Transition " << _prefix << "t" << transition->index << "\\n\");" << std::endl;
	
	padding += "  ";
	indent++;
	
	// iterators of history transitions executable content
	std::map<GlobalTransition*, std::pair<GlobalTransition::Action::iter_t, GlobalTransition::Action::iter_t> > actionIters;
	std::map<GlobalTransition*, std::set<GlobalTransition::Action> > actionsInTransition;

	typedef std::map<GlobalTransition*, std::pair<GlobalTransition::Action::iter_t, GlobalTransition::Action::iter_t> > actionIters_t;
	
	histIter = transition->historyTrans.begin();
	while(histIter != transition->historyTrans.end()) {
		actionIters.insert(std::make_pair((*histIter), std::make_pair((*histIter)->actions.begin(), (*histIter)->actions.end())));
		// add history transitions actions to the set
		for (std::list<GlobalTransition::Action>::iterator actionIter = (*histIter)->actions.begin(); actionIter != (*histIter)->actions.end(); actionIter++) {
			actionsInTransition[*histIter].insert(*actionIter);
		}
//		std::copy((*histIter)->actions.begin(), (*histIter)->actions.end(), std::inserter(actionsInTransition[*histIter], actionsInTransition[*histIter].begin()));
		histIter++;
	}
//	std::cout << "###" << std::endl;
	for (std::list<GlobalTransition::Action>::iterator actionIter = transition->actions.begin(); actionIter != transition->actions.end(); actionIter++) {
		actionsInTransition[transition].insert(*actionIter);
	}
//	std::copy(transition->actions.begin(), transition->actions.end(), std::inserter(actionsInTransition[transition], actionsInTransition[transition].begin()));

	
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
			if (histActionIter->second.first == histActionIter->second.second) // TODO: is this correct?
				continue;
			GlobalTransition::Action& histAction = *(histActionIter->second.first);

			// is the current action identical or a generated raise for done.state.ID?
//			std::cerr << baseAction << std::endl;
//			std::cerr << histAction << std::endl;
			if (baseAction != histAction && !baseAction.raiseDone) {
//				std::cout << baseAction << std::endl;
//				std::cout << histAction << std::endl;
				
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
		
		if (!isConditionalized && ecIter->type == ExecContentSeqItem::EXEC_CONTENT_ONLY_FOR) {
//			assert(!wroteHistoryAssignments); // we need to move assignments after dispatching?
			stream << padding << "if" << std::endl;
			stream << padding << ":: " << conditionalizeForHist(ecIter->transitions) << " -> {" << std::endl;
			padding += "  ";
			indent++;
			isConditionalized = true;
		} else if (!isConditionalized && ecIter->type == ExecContentSeqItem::EXEC_CONTENT_ALL_BUT) {
//			assert(!wroteHistoryAssignments); // we need to move assignments after dispatching?
			stream << padding << "if" << std::endl;
			stream << padding << ":: " << conditionalizeForHist(ecIter->transitions) << " -> skip;" << std::endl;
			stream << padding << ":: else -> {" << std::endl;
			padding += "  ";
			indent++;
			isConditionalized = true;
		}

#if 0
		switch (ecIter->type) {
		case ExecContentSeqItem::EXEC_CONTENT_ALL_BUT:
			std::cout << "ALL_BUT" << std::endl;
			break;
		case ExecContentSeqItem::EXEC_CONTENT_EVERY:
			std::cout << "EVERY" << std::endl;
			break;
		case ExecContentSeqItem::EXEC_CONTENT_ONLY_FOR:
			std::cout << "ONLY_FOR" << std::endl;
			break;
				
			default:
    break;
		}
#endif
		
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
			stream << "/* executable content for transition */" << std::endl;
			writeExecutableContent(stream, action.transition, indent);
//			continue;
		}
		
		if (action.onExit) {
//			std::cout<< action.onExit << std::endl;
			// executable content from an onexit element
			if (action.onExit.getParentNode()) // this should not be necessary?
				stream << "/* executable content for exiting state " << ATTR_CAST(action.onExit.getParentNode(), "id") << " */" << std::endl;
			writeExecutableContent(stream, action.onExit, indent);
//			continue;
		}
		
		if (action.onEntry) {
			// executable content from an onentry element
			if (action.onEntry.getParentNode()) // this should not be necessary?
				stream << "/* executable content for entering state " << ATTR_CAST(action.onEntry.getParentNode(), "id") << " */" << std::endl;
			writeExecutableContent(stream, action.onEntry, indent);
//			continue;
		}

		if (action.raiseDone) {
			// executable content from an onentry element
			if (action.raiseDone.getParentNode()) // this should not be necessary?
				stream << "/* raising done event for " << ATTR_CAST(action.raiseDone.getParentNode(), "id") << " */" << std::endl;
			writeExecutableContent(stream, action.raiseDone, indent);
			//			continue;
		}

		if (action.invoke) {
			// an invoke element
			
			if (_machines.find(action.invoke) != _machines.end()) {
				stream << padding << _prefix << "start!" << _analyzer->macroForLiteral(_machines[action.invoke]->_invokerid) << ";" << std::endl;
			} else {
				if (HAS_ATTR_CAST(action.invoke, "id")) {
					stream << padding << _prefix << ATTR_CAST(action.invoke, "id") << "Running = true;" << std::endl;
				}
			}

		}
		
		if (action.uninvoke) {
			if (_machines.find(action.uninvoke) != _machines.end()) {
				stream << padding << "do" << std::endl;
				stream << padding << ":: " << _prefix << "start??" << _analyzer->macroForLiteral(_machines[action.uninvoke]->_invokerid) << " -> skip" << std::endl;
				stream << padding << ":: else -> break;" << std::endl;
				stream << padding << "od" << std::endl;

				stream << padding << _machines[action.uninvoke]->_prefix << "canceled = true;" << std::endl;
				if (_analyzer->usesEventField("delay")) {
					stream << padding << "removePendingEventsForInvoker(" << _analyzer->macroForLiteral(_machines[action.uninvoke]->_invokerid) << ");" << std::endl;
				}
			} else {
				if (HAS_ATTR_CAST(action.uninvoke, "id")) {
					stream << padding << _prefix << ATTR_CAST(action.uninvoke, "id") << "Running = false;" << std::endl;
				}
			}
		}
		
		if (isConditionalized) {
			// peek into next content and see if same conditions apply -> keep conditionalization
			bool sameCondition = false;
			std::list<ExecContentSeqItem>::const_iterator nextIter = ecIter;
			nextIter++;
			if (nextIter != ecSeq.end() && ecIter->type == nextIter->type && ecIter->transitions == nextIter->transitions) {
				sameCondition = true;
			}
			
			if (!sameCondition) {
				padding = padding.substr(2);
				indent--;

				if (ecIter->type == ExecContentSeqItem::EXEC_CONTENT_ALL_BUT) {
					stream << padding << "}" << std::endl;
					stream << padding << "fi" << std::endl << std::endl;
				} else if(ecIter->type == ExecContentSeqItem::EXEC_CONTENT_ONLY_FOR) {
					stream << padding << "}" << std::endl;
					stream << padding << ":: else -> skip;" << std::endl;
					stream << padding << "fi;" << std::endl << std::endl;
				}
				isConditionalized = false;
			}
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

        if (!envVarIsTrue("USCXML_ANNOTATE_NOCOMMENT")) {
            stream << "/* to state ";
            FlatStateIdentifier flatActiveDest(histNewState->activeId);
            PRETTY_PRINT_LIST(stream, flatActiveDest.getActive());
            stream << " via history */" << std::endl;
        }

        stream << padding << ":: " << conditionalizeForHist(histTargetIter->second) << " -> " << _prefix << "s = s" << histNewState->activeIndex << ";" << std::endl;
//		writeTransitionClosure(stream, *histTargetIter->second.begin(), histNewState, indent + 1); // is this correct for everyone in set?


		hasHistoryTarget = true;
	}
	
	origNewState = _activeConf[transition->activeDestination];
	FlatStateIdentifier flatActiveDest(transition->activeDestination);
	assert(origNewState != NULL);
	
    if (!envVarIsTrue("USCXML_ANNOTATE_NOCOMMENT")) {
        stream << "/* to state ";
        PRETTY_PRINT_LIST(stream, flatActiveDest.getActive());
        stream <<  " */" << std::endl;
    }
	if (hasHistoryTarget) {
		stream << padding << ":: else -> ";
		padding += "  ";
		indent++;
	}
	
	stream << padding << _prefix << "s = s" << origNewState->activeIndex << ";" << std::endl;


	if (hasHistoryTarget) {
		padding = padding.substr(2);
		indent--;
//		stream << padding << "}" << std::endl;
		stream << padding << "fi;" << std::endl;
	}

    TRANSITION_TRACE(transition, false);
	
	padding = padding.substr(2);
    stream << padding << "}" << std::endl;

    // moved up here for goto from d_step
	writeTransitionClosure(stream, transition, origNewState, indent-1);

	_perfTransProcessed++;
	_perfTransTotal++;
	
	DUMP_STATS(false);

}

void ChartToPromela::writeHistoryAssignments(std::ostream& stream, GlobalTransition* transition, int indent) {
	std::string padding;
	for (int i = 0; i < indent; i++) {
		padding += "  ";
	}
	
	if (transition->historyTrans.size() == 0)
		return;
	
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
				histClasses.erase(innerHistClassIter++);
			} else {
				innerHistClassIter++;
			}
		}
		
		_perfHistoryProcessed++;
		_perfHistoryTotal++;

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
					stream << padding << _prefix << "_hist_" << boost::to_lower_copy(_analyzer->macroForLiteral(forgetIter->first));
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
					stream << padding << _prefix << "_hist_" << boost::to_lower_copy(_analyzer->macroForLiteral(rememberIter->first));
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
	if (from == to)
		return;
		
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

//	if (_traceTransitions) {
//		for (std::set<int>::iterator transRefIter = transition->transitionRefs.begin(); transRefIter != transition->transitionRefs.end(); transRefIter++) {
//			stream << padding << _prefix << "transitions[" << *transRefIter << "] = false; " << std::endl;
//		}
//	}

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
//		if (HAS_ATTR(nodeElem, "index"))
//			stream << padding << "  " << _prefix << ATTR(nodeElem, "index") << "++;" << std::endl;
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
		stream << beautifyIndentation(ADAPT_SRC(boost::trim_copy(assignTexts[0].getNodeValue())), indent) << std::endl;
		
	} else if(TAGNAME(nodeElem) == "send" || TAGNAME(nodeElem) == "raise") {
		std::string targetQueue;
        std::string insertOp = "!";
		if (TAGNAME(nodeElem) == "raise") {
			targetQueue = _prefix + "iQ";
		} else if (!HAS_ATTR(nodeElem, "target")) {
			if (_allowEventInterleaving) {
				targetQueue = _prefix + "tmpQ";
			} else {
				targetQueue = _prefix + "eQ";
			}
		} else if (ATTR(nodeElem, "target").compare("#_internal") == 0) {
			targetQueue = _prefix + "iQ";
		} else if (ATTR(nodeElem, "target").compare("#_parent") == 0) {
			targetQueue = _parent->_prefix + "eQ";
		} else if (boost::starts_with(ATTR(nodeElem, "target"), "#_") && _machinesPerId.find(ATTR(nodeElem, "target").substr(2)) != _machinesPerId.end()) {
			targetQueue = _machines[_machinesPerId[ATTR(nodeElem, "target").substr(2)]]->_prefix + "eQ";
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
                stream << _analyzer->getTypeReset("tmpE", _analyzer->getType("_event"), padding + "  ");
                stream << padding << "  tmpE.name = " << event << ";" << std::endl;
				
				if (HAS_ATTR(nodeElem, "idlocation")) {
					stream << padding << "  /* idlocation */" << std::endl;
					stream << padding << "  _lastSendId = _lastSendId + 1;" << std::endl;
					stream << padding << "  " << _prefix << ATTR(nodeElem, "idlocation") << " = _lastSendId;" << std::endl;
					stream << padding << "  tmpE.sendid = _lastSendId;" << std::endl;
					stream << padding << "  if" << std::endl;
					stream << padding << "  :: _lastSendId == 2147483647 -> _lastSendId = 0;" << std::endl;
					stream << padding << "  :: else -> skip;" << std::endl;
					stream << padding << "  fi;" << std::endl;
				} else if (HAS_ATTR(nodeElem, "id")) {
					stream << padding << "  tmpE.sendid = " << _analyzer->macroForLiteral(ATTR(nodeElem, "id")) << ";" << std::endl;
				}
				
				if (_invokerid.length() > 0) { // do not send invokeid if we send / raise to ourself
					stream << padding << "  tmpE.invokeid = " << _analyzer->macroForLiteral(_invokerid) << ";" << std::endl;
				}
				
				if (_analyzer->usesEventField("origintype") && !boost::ends_with(targetQueue, "iQ")) {
					stream << padding << "  tmpE.origintype = " << _analyzer->macroForLiteral("http://www.w3.org/TR/scxml/#SCXMLEventProcessor") << ";" << std::endl;
				}

				if (_analyzer->usesEventField("delay")) {
#if NEW_DELAY_RESHUFFLE
#else
                    insertOp += "!";
					stream << padding << "  _lastSeqId = _lastSeqId + 1;" << std::endl;
#endif
					if (HAS_ATTR_CAST(nodeElem, "delay")) {
						stream << padding << "  tmpE.delay = " << ATTR_CAST(nodeElem, "delay") << ";" << std::endl;
					} else if (HAS_ATTR_CAST(nodeElem, "delayexpr")) {
						stream << padding << "  tmpE.delay = " << ADAPT_SRC(ATTR_CAST(nodeElem, "delayexpr")) << ";" << std::endl;
					} else {
						stream << padding << "  tmpE.delay = 0;" << std::endl;
					}
#if NEW_DELAY_RESHUFFLE
#else
                    stream << padding << "  tmpE.seqNr = _lastSeqId;" << std::endl;
#endif
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
				stream << padding << "  " << targetQueue << insertOp <<"tmpE;" << std::endl;
                
#if NEW_DELAY_RESHUFFLE
                if (_analyzer->usesEventField("delay") && !boost::ends_with(targetQueue, "iQ")) {
                    stream << padding << "  insertWithDelay(" << targetQueue << ");" << std::endl;
                }
#endif
                
				stream << padding << "}" << std::endl;
			} else {
				stream << padding << targetQueue << insertOp << event << ";" << std::endl;
			}
		}
	} else if(TAGNAME(nodeElem) == "cancel") {
		if (HAS_ATTR(nodeElem, "sendid")) {
			stream << padding << "cancelSendId(" << _analyzer->macroForLiteral(ATTR(nodeElem, "sendid")) << ", " << (_invokerid.size() > 0 ? _analyzer->macroForLiteral(_invokerid) : "0") << ");" << std::endl;
		} else if (HAS_ATTR(nodeElem, "sendidexpr")) {
			stream << padding << "cancelSendId(" << ADAPT_SRC(ATTR(nodeElem, "sendidexpr")) << ", " << (_invokerid.size() > 0 ? _analyzer->macroForLiteral(_invokerid) : "0") << ");" << std::endl;
		}
	} else {
		std::cerr << "'" << TAGNAME(nodeElem) << "'" << std::endl << nodeElem << std::endl;
		assert(false);
	}
}

PromelaInlines::~PromelaInlines() {
	return;
}

std::list<PromelaInline*> PromelaInlines::getRelatedTo(const Arabica::DOM::Node<std::string>& node, PromelaInline::PromelaInlineType type) {
	std::list<PromelaInline*> related;
	
	std::map<Arabica::DOM::Node<std::string>, std::list<PromelaInline*> >::iterator inlIter = inlines.begin();
	while (inlIter != inlines.end()) {
		std::list<PromelaInline*>::iterator pmlIter = inlIter->second.begin();
		while (pmlIter != inlIter->second.end()) {
			if ((type != PromelaInline::PROMELA_NIL || (*pmlIter)->type == type) && (*pmlIter)->relatesTo(node)) {
				related.push_back(*pmlIter);
			}
			pmlIter++;
		}
		inlIter++;
	}
	return related;

	return related;
}

std::list<PromelaInline*> PromelaInlines::getAllOfType(uint32_t type) {
	std::list<PromelaInline*> related;
	
	std::map<Arabica::DOM::Node<std::string>, std::list<PromelaInline*> >::iterator inlIter = inlines.begin();
	while (inlIter != inlines.end()) {
		std::list<PromelaInline*>::iterator pmlIter = inlIter->second.begin();
		while (pmlIter != inlIter->second.end()) {
			if ((*pmlIter)->type & type) {
				related.push_back(*pmlIter);
			}
			pmlIter++;
		}
		inlIter++;
	}
	return related;
}

PromelaInline::PromelaInline(const Arabica::DOM::Node<std::string>& node) : prevSibling(NULL), nextSibling(NULL), type(PROMELA_NIL) {
	if (node.getNodeType() != Node_base::COMMENT_NODE && node.getNodeType() != Node_base::TEXT_NODE)
		return; // nothing to do

	std::stringstream ssLine(node.getNodeValue());
	std::string line;
	
	while(std::getline(ssLine, line)) {
		// skip to first promela line
		boost::trim(line);
		if (boost::starts_with(line, "promela"))
			break;
	}

	if (!boost::starts_with(line, "promela"))
		return;

	if (false) {
	} else if (boost::starts_with(line, "promela-code")) {
		type = PROMELA_CODE;
	} else if (boost::starts_with(line, "promela-ltl")) {
		type = PROMELA_LTL;
	} else if (boost::starts_with(line, "promela-event-all")) {
		type = PROMELA_EVENT_ALL_BUT;
	} else if (boost::starts_with(line, "promela-event")) {
		type = PROMELA_EVENT_ONLY;
	} else if (boost::starts_with(line, "promela-progress")) {
		type = PROMELA_PROGRESS_LABEL;
	} else if (boost::starts_with(line, "promela-accept")) {
		type = PROMELA_ACCEPT_LABEL;
	} else if (boost::starts_with(line, "promela-end")) {
		type = PROMELA_END_LABEL;
	}

	std::stringstream contentSS;
	size_t endType = line.find_first_of(": \n");
	
	std::string seperator;
	if (endType != std::string::npos && endType + 1 < line.size()) {
		contentSS << line.substr(endType + 1, line.size() - endType + 1);
		seperator = "\n";
	}
	
	while(std::getline(ssLine, line)) {
		boost::trim(line);
		if (boost::starts_with(line, "promela")) {
			std::cerr << "Split multiple #promela pragmas into multiple comments!" << std::endl;
			break;
		}
		contentSS << seperator << line;
		seperator = "\n";
	}
	content = contentSS.str();
}


PromelaInlines::PromelaInlines(const Arabica::DOM::Node<std::string>& node) {
	NodeSet<std::string> levelNodes;
	levelNodes.push_back(node);
	
	size_t level = 0;
	while(levelNodes.size() > 0) {
		PromelaInline* predecessor = NULL;

		// iterate all nodes at given level
		for (int i = 0; i < levelNodes.size(); i++) {
			
			// get all comments
			NodeSet<std::string> comments = InterpreterImpl::filterChildType(Node_base::COMMENT_NODE, levelNodes[i]);
			for (int j = 0; j < comments.size(); j++) {
				PromelaInline* tmp = new PromelaInline(comments[j]);
				if (tmp->type == PromelaInline::PROMELA_NIL) {
					delete tmp;
					continue;
				}

				if (predecessor != NULL) {
					tmp->prevSibling = predecessor;
					predecessor->nextSibling = tmp;
				}
				tmp->level = level;
				tmp->container = Element<std::string>(levelNodes[i]);
				predecessor = tmp;
				inlines[levelNodes[i]].push_back(tmp);
				allInlines.push_back(tmp);
			}
		}
		
		levelNodes = InterpreterImpl::filterChildType(Node_base::ELEMENT_NODE, levelNodes);
		level++;
	}
}

void PromelaInline::dump() {
#if 0
	switch(type) {
		case PROMELA_NIL:
			std::cerr << "PROMELA_NIL" << std::endl;
			break;
		case PROMELA_CODE:
			std::cerr << "PROMELA_CODE" << std::endl;
			break;
		case PROMELA_EVENT_SOURCE_ALL:
			std::cerr << "PROMELA_EVENT_SOURCE" << std::endl;
			break;
		case PROMELA_INVOKER:
			std::cerr << "PROMELA_INVOKER" << std::endl;
			break;
		case PROMELA_PROGRESS_LABEL:
			std::cerr << "PROMELA_PROGRESS_LABEL" << std::endl;
			break;
		case PROMELA_ACCEPT_LABEL:
			std::cerr << "PROMELA_ACCEPT_LABEL" << std::endl;
			break;
		case PROMELA_END_LABEL:
			std::cerr << "PROMELA_END_LABEL" << std::endl;
			break;
	}
#endif
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

	stream << "/* global variables " << (_prefix.size() > 0 ? "for " + _prefix : "") << " */" << std::endl;
	
	// we cannot know our event queue with nested invokers? Adding some for test422
	size_t tolerance = 6;
	
	if (_analyzer->usesComplexEventStruct()) {
		// event is defined with the typedefs
		stream << "_event_t " << _prefix << "_event;               /* current event */" << std::endl;
		stream << "unsigned " << _prefix << "s : " << BIT_WIDTH(_activeConf.size() + 1) << ";                /* current state */" << std::endl;
		stream << "chan " << _prefix << "iQ   = [" << MAX(_internalQueueLength, 1) << "] of {_event_t}  /* internal queue */" << std::endl;
		stream << "chan " << _prefix << "eQ   = [" << _externalQueueLength + tolerance << "] of {_event_t}  /* external queue */" << std::endl;
		if (_allowEventInterleaving)
			stream << "chan " << _prefix << "tmpQ = [" << MAX(_externalQueueLength + tolerance, 1) << "] of {_event_t}  /* temporary queue for external events in transitions */" << std::endl;
	} else {
		stream << "unsigned " << _prefix << "_event : " << BIT_WIDTH(_analyzer->getEvents().size() + 1) << ";                /* current event */" << std::endl;
		stream << "unsigned " << _prefix << "s : " << BIT_WIDTH(_activeConf.size() + 1) << ";            /* current state */" << std::endl;
		stream << "chan " << _prefix << "iQ   = [" << MAX(_internalQueueLength, 1) << "] of {int}  /* internal queue */" << std::endl;
		stream << "chan " << _prefix << "eQ   = [" << _externalQueueLength + tolerance << "] of {int}  /* external queue */" << std::endl;
		if (_allowEventInterleaving)
			stream << "chan " << _prefix << "tmpQ = [" << MAX(_externalQueueLength + tolerance, 1) << "] of {int}  /* temporary queue for external events in transitions */" << std::endl;
//		stream << "hidden unsigned " << _prefix << "tmpQItem : " << BIT_WIDTH(_analyzer->getEvents().size() + 1) << ";" << std::endl;
	}
	if (_machines.size() > 0) {
		stream << "chan " << _prefix << "start = [" << _machines.size() << "] of {int}  /* nested machines to start at next macrostep */" << std::endl;
	}
	
	if (_hasIndexLessLoops)
		stream << "hidden int " << _prefix << "_index;             /* helper for indexless foreach loops */" << std::endl;

	stream << "hidden int " << _prefix << "procid;             /* the process id running this machine */" << std::endl;
	stream << "bool " << _prefix << "spontaneous;              /* whether to take spontaneous transitions */" << std::endl;
	stream << "bool " << _prefix << "done;                     /* is the state machine stopped? */" << std::endl;
	stream << "bool " << _prefix << "canceled;                 /* is the state machine canceled? */" << std::endl;

	if (_traceTransitions)
		stream << "bool " << _prefix << "transitions[" << indexedTransitions.size() << "];             /* transitions in the optimal transition set */" << std::endl;

	if (_analyzer->getTypes().types.find("_ioprocessors") != _analyzer->getTypes().types.end()) {
		stream << "hidden _ioprocessors_t " << _prefix << "_ioprocessors;" << std::endl;
		_varInitializers.push_front("_ioprocessors.scxml.location = " + (_invokerid.size() > 0 ? _analyzer->macroForLiteral(_invokerid) : "1") + ";");
	}
	
	if (_prefix.size() == 0 || _prefix == "MAIN_") {
		if (_analyzer->usesEventField("sendid")) {
//			stream << "chan sendIdQ = [" << MAX(_externalQueueLength + 1, 1) << "] of {_event_t}  /* temporary queue to cancel events per sendidexpr */" << std::endl;
			stream << "hidden int _lastSendId = 0;         /* sequential counter for send ids */" << std::endl;
		}

		if (_analyzer->usesEventField("delay")) {
#if NEW_DELAY_RESHUFFLE
#else
			stream << "hidden int _lastSeqId = 0;     /* sequential counter for delayed events */"  << std::endl;
#endif
		}
	}
//	if (_analyzer->usesPlatformVars()) {
//		stream << "_x_t _x;" << std::endl;
//	}

	if (_analyzer->usesInPredicate()) {
		stream << "_x_t " << _prefix << "_x;" << std::endl;
	}

	std::list<PromelaInline*> pmls = pmlInlines.getAllOfType(PromelaInline::PROMELA_EVENT_ALL_BUT | PromelaInline::PROMELA_EVENT_ONLY);
	for (std::list<PromelaInline*>::iterator pmlIter = pmls.begin(); pmlIter != pmls.end(); pmlIter++) {
		if ((*pmlIter)->container && LOCALNAME((*pmlIter)->container) == "invoke") {
			stream << "bool " << _prefix << ATTR_CAST((*pmlIter)->container, "id") << "Running;" << std::endl;
		}
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
		
		if (typeIter->first == "_event" ||
				typeIter->first == "_x" ||
				typeIter->first == "_ioprocessors" ||
				typeIter->first == "_SESSIONID" ||
				typeIter->first == "_NAME") {
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
	
}

void ChartToPromela::writeEventSources(std::ostream& stream) {
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
				stream << padding << invoker->_prefix << *nlIter << " = " << _prefix << *nlIter << ";" << std::endl;
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
    stream << "  d_step {" << std::endl;
    stream << "    " << _prefix << "done = false;" << std::endl;
	stream << "    " << _prefix << "canceled = false;" << std::endl;
	stream << "    " << _prefix << "spontaneous = true;" << std::endl;
	stream << "    " << _prefix << "procid = _pid;" << std::endl;
    stream << "  }" << std::endl;
	// write initial transition
//	transitions = filterChildElements(_nsInfo.xmlNSPrefix + "transition", _startState);
//	assert(transitions.size() == 1);

	NodeSet<std::string> scripts = filterChildElements(_nsInfo.xmlNSPrefix + "script", _scxml, false);
	if (scripts.size() > 0) {
		stream << std::endl << "/* global scripts */" << std::endl;
		for (int i = 0; i < scripts.size(); i++) {
			writeExecutableContent(stream, scripts[i], 1);
		}
		stream << std::endl;
	}
	
	stream << std::endl << "/* transition to initial state */" << std::endl;
	assert(_start->sortedOutgoing.size() == 1);
	// initial transition has to be first one for control flow at start
	writeTransition(stream, _start->sortedOutgoing.front(), 1);
	stream << std::endl;
	
	// every other transition
	for (std::map<std::string, GlobalState*>::iterator stateIter = _activeConf.begin(); stateIter != _activeConf.end(); stateIter++) {
		for (std::list<GlobalTransition*>::iterator transIter = stateIter->second->sortedOutgoing.begin(); transIter != stateIter->second->sortedOutgoing.end(); transIter++) {
			// don't write invalid transition
			if (!(*transIter)->isValid) {
				LOG(ERROR) << "Sorted outgoing transitions contains invalid transitions - did you instruct ChartToFSM to keep those?";
				abort();
			}

			// don't write initial transition
			if (_start->sortedOutgoing.front() == *transIter)
				continue;
			// don't write trivial or history transitions
			if ((*transIter)->historyBase == NULL) // TODO!
//				if ((*transIter)->hasExecutableContent && (*transIter)->historyBase == NULL)
				writeTransition(stream, *transIter, 1);
		}
		_perfStatesProcessed++;
		_perfStatesTotal++;
		
		DUMP_STATS(false);
	}
	DUMP_STATS(true);

	stream << std::endl;
	stream << _prefix << "macroStep: skip;" << std::endl;
	if (_allowEventInterleaving) {
		stream << "  /* push send events to external queue - this needs to be interleavable! */" << std::endl;
		stream << "  do" << std::endl;
		if (_analyzer->usesEventField("delay")) {
#if NEW_DELAY_RESHUFFLE
			stream << "  :: len(" << _prefix << "tmpQ) != 0 -> { " << _prefix << "tmpQ?" << _prefix << "_event; " << _prefix << "eQ!" << _prefix << "_event; insertWithDelay(" << _prefix << "eQ); }" << std::endl;
#else
            stream << "  :: len(" << _prefix << "tmpQ) != 0 -> { " << _prefix << "tmpQ?" << _prefix << "_event; " << _prefix << "eQ!!" << _prefix << "_event }" << std::endl;
#endif
        } else {
			stream << "  :: len(" << _prefix << "tmpQ) != 0 -> { " << _prefix << "tmpQ?" << _prefix << "_event; " << _prefix << "eQ!" << _prefix << "_event }" << std::endl;
		}
		stream << "  :: else -> break;" << std::endl;
		stream << "  od;" << std::endl << std::endl;
	}
	
	if (_machines.size() > 0) {
		stream << "  /* start pending invokers */" << std::endl;
		stream << "  int invokerId;" << std::endl;
		stream << "  do" << std::endl;
		stream << "  :: " << _prefix << "start?invokerId -> {" << std::endl;
		stream << "    if " << std::endl;
		for (std::map<Arabica::DOM::Node<std::string>, ChartToPromela*>::iterator machIter = _machines.begin(); machIter != _machines.end(); machIter++) {
			stream << "    :: invokerId == " << _analyzer->macroForLiteral(machIter->second->_invokerid) << " -> {" << std::endl;
			writeStartInvoker(stream, machIter->first, machIter->second, 3);
			stream << "    }" << std::endl;
		}
		stream << "    :: else -> skip; " << std::endl;
		stream << "    fi " << std::endl;
		stream << "  }" << std::endl;
		stream << "  :: else -> break;" << std::endl;
		stream << "  od" << std::endl << std::endl;
	}
	
	if (_analyzer->usesEventField("delay") && _machinesAll->size() > 1) {
		stream << "/* Determine machines with smallest delay and set their process priority */" << std::endl;
		stream << "  scheduleMachines();" << std::endl << std::endl;
	}
	
	std::list<PromelaInline*> eventSources = pmlInlines.getAllOfType(PromelaInline::PROMELA_EVENT_ALL_BUT |
																																	 PromelaInline::PROMELA_EVENT_ONLY);
	
	stream << "  atomic {" << std::endl;
	stream << "    /* pop an event */" << std::endl;
	stream << "    if" << std::endl;
	stream << "    :: len(" << _prefix << "iQ) != 0 -> " << _prefix << "iQ ? " << _prefix << "_event   /* from internal queue */" << std::endl;
	if (eventSources.size() > 0) {
		stream << "    :: len(" << _prefix << "eQ) != 0 -> " << _prefix << "eQ ? " << _prefix << "_event   /* from external queue */" << std::endl;
		stream << "    :: else -> {" << std::endl;
		stream << "      /* external queue is empty -> automatically enqueue external event */" << std::endl;
		stream << "      if" << std::endl;

		for (std::list<PromelaInline*>::iterator esIter = eventSources.begin(); esIter != eventSources.end(); esIter++) {
			PromelaEventSource es(**esIter);

			std::string condition = "true";
			
			if (LOCALNAME(es.container) == "invoke") {
				if (HAS_ATTR_CAST(es.container, "id")) {
					condition = _prefix + ATTR_CAST(es.container, "id") + "Running";
				} else {
					LOG(ERROR) << "Invoker has no id";
				}
			} else if (HAS_ATTR(es.container, "id")) {
				condition = _prefix + "_x.states[" + _analyzer->macroForLiteral(ATTR(es.container, "id")) + "]";
			}
			stream << "      :: " << condition << " -> {" << std::endl;
			
			if (es.type == PromelaInline::PROMELA_EVENT_ALL_BUT) {
				std::string excludeEventDescs;
				for (std::list<Data>::iterator evIter = es.events.array.begin(); evIter != es.events.array.end(); evIter++) {
					excludeEventDescs += " " + evIter->atom;
				}
				
				NodeSet<std::string> transitions = filterChildElements("transition", es.container, true);
				std::set<std::string> eventNames;
				for (int i = 0; i < transitions.size(); i++) {
					if (!HAS_ATTR_CAST(transitions[i], "event"))
						continue;
					if (HAS_ATTR_CAST(transitions[i], "cond") && ATTR_CAST(transitions[i], "cond").find("_event.") != std::string::npos)
						continue;
					std::list<std::string> events = InterpreterImpl::tokenizeIdRefs(ATTR_CAST(transitions[i], "event"));
					for (std::list<std::string>::iterator evIter = events.begin(); evIter != events.end(); evIter++) {
						std::string eventName = *evIter;
						if (boost::ends_with(eventName, "*"))
							eventName = eventName.substr(0, eventName.size() - 1);
						if (boost::ends_with(eventName, "."))
							eventName = eventName.substr(0, eventName.size() - 1);

						// is this event excluded?
						if (!InterpreterImpl::nameMatch(excludeEventDescs, eventName)) {
							eventNames.insert(eventName);
						}
					}
				}

				if (eventNames.size() > 0) {
					stream << "        if " << std::endl;
					for (std::set<std::string>::iterator evIter = eventNames.begin(); evIter != eventNames.end(); evIter++) {
						stream << "        :: true -> { " << _prefix << "_event" << (_analyzer->usesComplexEventStruct() ? ".name" : "")<< " = " << _analyzer->macroForLiteral(*evIter) << " }" << std::endl;
					}
					stream << "        fi " << std::endl;
				}
				
			} else if (es.type == PromelaInline::PROMELA_EVENT_ONLY) {
				if (es.events.array.size() > 0) {
					stream << "        if " << std::endl;
					for (std::list<Data>::iterator evIter = es.events.array.begin(); evIter != es.events.array.end(); evIter++) {
						stream << "        :: true -> { " << std::endl;
						stream << dataToAssignments("          _event", *evIter);
						stream << "        } " << std::endl;
					}
					stream << "        fi " << std::endl;
				} else {
					stream << dataToAssignments("        _event", es.events);
				}
			} else {
				assert(false);
			}
			stream << "      }" << std::endl;
		}
		
		stream << "      fi" << std::endl;
		stream << "    }" << std::endl;
	} else {
		stream << "    :: else -> " << _prefix << "eQ ? " << _prefix << "_event           /* from external queue */" << std::endl;
	}
	stream << "    fi;" << std::endl << std::endl;

	
	stream << "    /* terminate if we are stopped */" << std::endl;
	stream << "    if" << std::endl;
	stream << "    :: " << _prefix << "done -> goto " << _prefix << "terminate;" << std::endl;
	if (_parent != NULL) {
		stream << "    :: " << _prefix << "canceled -> goto " << _prefix << "cancel;" << std::endl;
	}
	stream << "    :: else -> skip;" << std::endl;
	stream << "    fi;" << std::endl << std::endl;

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
			stream << "/* <finalize> event */" << std::endl;
			stream << "    if" << std::endl;
			for (std::map<Arabica::DOM::Node<std::string>, ChartToPromela*>::iterator invIter = _machines.begin(); invIter != _machines.end(); invIter++) {
				NodeSet<std::string> finalizes = filterChildElements(_nsInfo.xmlNSPrefix + "finalize", invIter->first, false);
				if (finalizes.size() > 0) {
					stream << "    :: " << _prefix << "_event.invokeid == " << _analyzer->macroForLiteral(invIter->second->_invokerid) << " -> {" << std::endl;
					writeExecutableContent(stream, finalizes[0], 3);
					stream << "    } " << std::endl;
				}
			}
			stream << "    :: else -> skip;" << std::endl;
			stream << "    fi;" << std::endl << std::endl;
		}
	}
	
	for (std::map<Arabica::DOM::Node<std::string>, ChartToPromela*>::iterator invIter = _machines.begin(); invIter != _machines.end(); invIter++) {
		if (invIter->second == this) {
			continue;
		}
		//std::cout << invIter->first << std::endl;
		if (stringIsTrue(ATTR_CAST(invIter->first, "autoforward"))) {
			stream << "/* autoforward event to " << invIter->second->_invokerid << " invokers */" << std::endl;
			stream << "    if" << std::endl;
			stream << "    :: " << invIter->second->_prefix << "done -> skip;" << std::endl;
			stream << "    :: " << invIter->second->_prefix << "canceled -> skip;" << std::endl;
#if NEW_DELAY_RESHUFFLE
            stream << "    :: else -> { " << invIter->second->_prefix << "eQ!" << _prefix << "_event" << "; insertWithDelay(" << invIter->second->_prefix << "eQ" << "); }" << std::endl;
#else
            stream << "    :: else -> { " << invIter->second->_prefix << "eQ!!" << _prefix << "_event" << " }" << std::endl;
#endif
			stream << "    fi;" << std::endl << std::endl;

		}
	}
	stream << std::endl;
	
	stream << _prefix << "microStep:" << std::endl;
	stream << "/* event dispatching per state */" << std::endl;
	stream << "    if" << std::endl;

	writeEventDispatching(stream);

	stream << "/* this is an error as we dispatched all valid states */" << std::endl;
	stream << "    :: else -> assert(false);" << std::endl;
	stream << "    fi;" << std::endl;
	stream << std::endl;
	stream << _prefix << "terminate: skip;" << std::endl;

	if (_parent != NULL) {
		stream << "    {" << std::endl;
        stream << _analyzer->getTypeReset("tmpE", _analyzer->getType("_event"), "      ");
		stream << "      tmpE.name = " << _analyzer->macroForLiteral("done.invoke." + _invokerid) << ";" << std::endl;
		if (_invokerid.length() > 0) {
			stream << "      tmpE.invokeid = " << _analyzer->macroForLiteral(_invokerid) << ";" << std::endl;
		}
		if (_analyzer->usesEventField("delay")) {
#if NEW_DELAY_RESHUFFLE
            stream << "      " << _parent->_prefix << "eQ!tmpE;" << std::endl;
            stream << "      insertWithDelay(" << _parent->_prefix << "eQ);" << std::endl;
            
#else
            stream << "      _lastSeqId = _lastSeqId + 1;" << std::endl;
            stream << "      tmpE.seqNr = _lastSeqId;" << std::endl;
            stream << "      " << _parent->_prefix << "eQ!!tmpE;" << std::endl;
#endif
        } else {
			stream << "      " << _parent->_prefix << "eQ!tmpE;" << std::endl;
		}
		stream << "    }" << std::endl;
		stream << _prefix << "cancel: skip;" << std::endl;
		if (_analyzer->usesEventField("delay"))
			stream << "    removePendingEventsForInvoker(" << _analyzer->macroForLiteral(this->_invokerid) << ")" << std::endl;
	}
	
	stream << "  }" << std::endl;
	stream << "}" << std::endl;
}

void ChartToPromela::writeRescheduleProcess(std::ostream& stream, int indent) {
	std::string padding;
	for (int i = 0; i < indent; i++) {
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

void ChartToPromela::writeDetermineShortestDelay(std::ostream& stream, int indent) {
	std::string padding;
	for (int i = 0; i < indent; i++) {
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

void ChartToPromela::writeInsertWithDelay(std::ostream& stream, int indent) {
    std::string padding;
    for (int i = 0; i < indent; i++) {
        padding += "  ";
    }
    
    uint32_t maxExternalQueueLength = 1;
    std::map<Arabica::DOM::Node<std::string>, ChartToPromela*>::iterator machineIter = _machinesAll->begin();
    while(machineIter != _machinesAll->end()) {
        maxExternalQueueLength = std::max(maxExternalQueueLength, machineIter->second->_externalQueueLength);
        machineIter++;
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
    stream << padding << "" << std::endl;
    stream << padding << "      /* move all events but last over and remember the last one */" << std::endl;
    stream << padding << "      _iwdIdx1 = 0;" << std::endl;
    stream << padding << "      _iwdQLength = len(queue) - 1;" << std::endl;
    stream << padding << "" << std::endl;
    stream << padding << "      do" << std::endl;
    stream << padding << "      :: _iwdIdx1 < _iwdQLength -> {" << std::endl;
    stream << padding << "        queue?_iwdTmpE;" << std::endl;
    stream << padding << "        _iwdQ[_iwdIdx1].name = _iwdTmpE.name;" << std::endl;

    stream << _analyzer->getTypeAssignment("_iwdQ[_iwdIdx1]", "_iwdTmpE", _analyzer->getType("_event"), padding + "        ");
    
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

    stream << _analyzer->getTypeAssignment("_iwdTmpE", "_iwdQ[_iwdIdx2]", _analyzer->getType("_event"), padding + "        ");
    
    stream << padding << "" << std::endl;
    stream << padding << "        if" << std::endl;
    stream << padding << "        :: _iwdTmpE.delay > _iwdLastE.delay -> {" << std::endl;
    stream << padding << "          queue!_iwdLastE;" << std::endl;
    stream << padding << "          _iwdInserted = true;" << std::endl;
    stream << padding << "        }" << std::endl;
    stream << padding << "        :: else -> skip" << std::endl;
    stream << padding << "        fi;" << std::endl;
    stream << padding << "" << std::endl;
    stream << padding << "        queue!_iwdTmpE;" << std::endl;
    stream << padding << "        _iwdIdx2++;" << std::endl;
    stream << padding << "      }" << std::endl;
    stream << padding << "      :: else -> break;" << std::endl;
    stream << padding << "      od" << std::endl;
    stream << padding << "" << std::endl;
    stream << padding << "      if" << std::endl;
    stream << padding << "      :: !_iwdInserted -> queue!_iwdLastE;" << std::endl;
    stream << padding << "      :: else -> skip;" << std::endl;
    stream << padding << "      fi;" << std::endl;
    stream << padding << "" << std::endl;
    stream << padding << "    }" << std::endl;
    stream << padding << "    :: else -> skip;" << std::endl;
    stream << padding << "    fi;" << std::endl;
    stream << padding << "  }" << std::endl;
    stream << padding << "}" << std::endl;
}

void ChartToPromela::writeAdvanceTime(std::ostream& stream, int indent) {
	std::string padding;
	for (int i = 0; i < indent; i++) {
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

void ChartToPromela::writeRemovePendingEventsFromInvoker(std::ostream& stream, int indent) {
	std::list<std::string> queues;
	queues.push_back("eQ");
	if (_allowEventInterleaving)
		queues.push_back("tmpQ");
	
	stream << "inline removePendingEventsForInvoker(invokeIdentifier) {" << std::endl;
	for (std::map<Arabica::DOM::Node<std::string>, ChartToPromela*>::iterator queueIter = _machinesAll->begin(); queueIter != _machinesAll->end(); queueIter++) {
		for (std::list<std::string>::iterator qIter = queues.begin(); qIter != queues.end(); qIter++) {
			stream << "  removePendingEventsForInvokerOnQueue(invokeIdentifier, " << queueIter->second->_prefix << *qIter << ");" << std::endl;
		}
	}
	stream << "}" << std::endl;
	stream << std::endl;

	stream << "inline removePendingEventsForInvokerOnQueue(invokeIdentifier, queue) {" << std::endl;
	stream << "  tmpIndex = 0;" << std::endl;
//    stream << _analyzer->getTypeReset("tmpE", _analyzer->getType("_event"), "  ");
	stream << "  do" << std::endl;
	stream << "  :: tmpIndex < len(queue) -> {" << std::endl;
	stream << "    queue?tmpE;" << std::endl;
	stream << "    if" << std::endl;
	stream << "    :: tmpE.delay == 0 || tmpE.invokeid != invokeIdentifier -> queue!tmpE;" << std::endl;
	stream << "    :: else -> skip;" << std::endl;
	stream << "    fi" << std::endl;
	stream << "    tmpIndex++;" << std::endl;
	stream << "  }" << std::endl;
	stream << "  :: else -> break;" << std::endl;
	stream << "  od" << std::endl;
	stream << "}" << std::endl;
}

void ChartToPromela::writeCancelEvents(std::ostream& stream, int indent) {
	std::list<std::string> queues;
	queues.push_back("eQ");
	if (_allowEventInterleaving)
		queues.push_back("tmpQ");

	stream << "inline cancelSendId(sendIdentifier, invokerIdentifier) {" << std::endl;
	for (std::map<Arabica::DOM::Node<std::string>, ChartToPromela*>::iterator queueIter = _machinesAll->begin(); queueIter != _machinesAll->end(); queueIter++) {
		for (std::list<std::string>::iterator qIter = queues.begin(); qIter != queues.end(); qIter++) {
			stream << "  cancelSendIdOnQueue(sendIdentifier, " << queueIter->second->_prefix << *qIter << ", invokerIdentifier);" << std::endl;
		}
	}
	stream << "}" << std::endl;
	stream << std::endl;


	stream << "inline cancelSendIdOnQueue(sendIdentifier, queue, invokerIdentifier) {" << std::endl;
	stream << "  tmpIndex = 0;" << std::endl;
//    stream << _analyzer->getTypeReset("tmpE", _analyzer->getType("_event"), "  ");
	stream << "  do" << std::endl;
	stream << "  :: tmpIndex < len(queue) -> {" << std::endl;
	stream << "    queue?tmpE;" << std::endl;
	stream << "    if" << std::endl;
	stream << "    :: tmpE.invokeid != invokerIdentifier || tmpE.sendid != sendIdentifier || tmpE.delay == 0 -> queue!tmpE;" << std::endl;
	stream << "    :: else -> skip;" << std::endl;
	stream << "    fi" << std::endl;
	stream << "    tmpIndex++;" << std::endl;
	stream << "  }" << std::endl;
	stream << "  :: else -> break;" << std::endl;
	stream << "  od" << std::endl;
	stream << "}" << std::endl;
}

void ChartToPromela::writeScheduleMachines(std::ostream& stream, int indent) {
	std::string padding;
	for (int i = 0; i < indent; i++) {
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
	
	for (std::map<Arabica::DOM::Node<std::string>, ChartToPromela*>::iterator queueIter = _machinesAll->begin(); queueIter != _machinesAll->end(); queueIter++) {
		for (std::list<std::string>::iterator qIter = queues.begin(); qIter != queues.end(); qIter++) {
			stream << "    determineSmallestDelay(smallestDelay, " << queueIter->second->_prefix << *qIter << ");" << std::endl;
		}
	}
	//		stream << "    printf(\"======= Lowest delay is %d\\n\", smallestDelay);" << std::endl;
	
	stream << std::endl << "/* prioritize processes with lowest delay or internal events */" << std::endl;
	
	for (std::map<Arabica::DOM::Node<std::string>, ChartToPromela*>::iterator queueIter = _machinesAll->begin(); queueIter != _machinesAll->end(); queueIter++) {
		stream << "    rescheduleProcess(smallestDelay, "
		<< queueIter->second->_prefix << "procid, "
		<< queueIter->second->_prefix << "iQ, "
		<< queueIter->second->_prefix << "eQ";
		if (_allowEventInterleaving) {
			stream << ", " << queueIter->second->_prefix << "tmpQ);" << std::endl;
		} else {
			stream << ");" << std::endl;
		}
	}
	
	stream << std::endl << "/* advance time by subtracting the smallest delay from all event delays */" << std::endl;
	stream << "    if" << std::endl;
	stream << "    :: (smallestDelay > 0) -> {" << std::endl;
	for (std::map<Arabica::DOM::Node<std::string>, ChartToPromela*>::iterator queueIter = _machinesAll->begin(); queueIter != _machinesAll->end(); queueIter++) {
		for (std::list<std::string>::iterator qIter = queues.begin(); qIter != queues.end(); qIter++) {
			stream << "      advanceTime(smallestDelay, " << queueIter->second->_prefix << *qIter << ");" << std::endl;
		}
	}
	stream << "    }" << std::endl;
	stream << "    :: else -> skip;" << std::endl;
	stream << "    fi;" << std::endl;
	stream << "  }" << std::endl;
	stream << "  set_priority(_pid, 10);" << std::endl << std::endl;
	stream << padding << "}" << std::endl;
}
	
void ChartToPromela::writeEventDispatching(std::ostream& stream) {
	for (std::map<std::string, GlobalState*>::iterator stateIter = _activeConf.begin(); stateIter != _activeConf.end(); stateIter++) {
		
		const std::string& stateId = stateIter->first;
		const GlobalState* state = stateIter->second;
		
		stream << std::endl << "/* ### current state ";
		FlatStateIdentifier flatActiveSource(stateId);
		PRETTY_PRINT_LIST(stream, flatActiveSource.getActive());
		stream << " ######################## */" << std::endl;

		stream << "    :: (" << _prefix << "s == s" << state->activeIndex << ") -> {" << std::endl;

		writeDispatchingBlock(stream, state->sortedOutgoing, 3);
		stream << "    }" << std::endl;
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
        if (!envVarIsTrue("USCXML_ANNOTATE_NOCOMMENT")) {
            stream << "/* transition to ";
            FlatStateIdentifier flatActiveSource(currTrans->activeDestination);
            PRETTY_PRINT_LIST(stream, flatActiveSource.getActive());
            stream << " */" << std::endl;
        }
        
		if (_traceTransitions) {
			for (std::set<int>::iterator transRefIter = currTrans->transitionRefs.begin(); transRefIter != currTrans->transitionRefs.end(); transRefIter++) {
				stream << padding << "  " << _prefix << "transitions[" << *transRefIter << "] = true; " << std::endl;
			}
		}
		
		stream << padding << "  goto " << _prefix << "t" << currTrans->index << ";" << std::endl;
		stream << padding << "}" << std::endl;

	} else {
		
		stream << " -> {" << std::endl;
		GlobalState* newState = _activeConf[currTrans->activeDestination];
		assert(newState != NULL);

        if (!envVarIsTrue("USCXML_ANNOTATE_NOCOMMENT")) {
            stream << "/* new state ";
            FlatStateIdentifier flatActiveDest(currTrans->activeDestination);
            PRETTY_PRINT_LIST(stream, flatActiveDest.getActive());
            stream <<  " */" << std::endl;
        }
		stream << padding << "  " << _prefix << "s = s" << newState->activeIndex << ";" << std::endl;

        TRANSITION_TRACE(currTrans, false);
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

//	_analyzer->addCode("bumpDownArrow = 1; _event.foo = 3; forgetSelectedServer = 1;", this);
//	exit(0);
	
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
		NodeSet<std::string> cancels = filterChildElements(_nsInfo.xmlNSPrefix + "cancel", _scxml, true);
		
		if (cancels.size() > 0) {
			_analyzer->addCode("_event.invokeid", this);
		}
		
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
#if NEW_DELAY_RESHUFFLE
#else
                _analyzer->addCode("_event.seqNr", this);
#endif
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
	
	{
		// gather all inline promela comments
		pmlInlines = PromelaInlines(_scxml);
		if (pmlInlines.getAllOfType(PromelaInline::PROMELA_EVENT_ONLY).size() > 0)
			_analyzer->addCode("_x.states", this);
		
		// register events and string literals
		for (std::list<PromelaInline*>::iterator inlIter = pmlInlines.allInlines.begin(); inlIter != pmlInlines.allInlines.end(); inlIter++) {
			if ((*inlIter)->type != (PromelaInline::PROMELA_EVENT_ONLY))
				continue;
			
			Data json = Data::fromJSON((*inlIter)->content);
			if (!json.empty()) {
				std::list<std::string> eventNames = PromelaInlines::getEventNames(json);
				for (std::list<std::string>::iterator evIter = eventNames.begin(); evIter != eventNames.end(); evIter++) {
					_analyzer->addEvent(*evIter);
				}
				
				std::list<std::string> stringLiterals = PromelaInlines::getStringLiterals(json);
				for (std::list<std::string>::iterator strIter = stringLiterals.begin(); strIter != stringLiterals.end(); strIter++) {
					_analyzer->addLiteral(*strIter);
				}
				
				if (json.array.size() > 0) {
					for (int i = 0; i < json.array.size(); i++) {
						std::string expr = dataToAssignments("_event", json.item(i));
						_analyzer->addCode(expr, this);
					}
				} else {
					std::string expr = dataToAssignments("_event", json);
					_analyzer->addCode(expr, this);
				
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
			} else {
				_hasIndexLessLoops = true;
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

std::list<std::string> PromelaInlines::getStringLiterals(const Data& data) {
	std::list<std::string> literals;
	if (data.atom.size() > 0 && data.type == Data::VERBATIM) {
		literals.push_back(data.atom);
	}
	if (data.array.size() > 0) {
		for (std::list<Data>::const_iterator arrIter = data.array.begin(); arrIter != data.array.end(); arrIter++) {
			std::list<std::string> nested = getStringLiterals(*arrIter);
			literals.insert(literals.end(), nested.begin(), nested.end());
		}
	}
	if (data.compound.size() > 0) {
		for (std::map<std::string, Data>::const_iterator compIter = data.compound.begin(); compIter != data.compound.end(); compIter++) {
			std::list<std::string> nested = getStringLiterals(compIter->second);
			literals.insert(literals.end(), nested.begin(), nested.end());
		}
	}
	return literals;
}

std::list<std::string> PromelaInlines::getEventNames(const Data& data) {
	std::list<std::string> eventNames;
	if (data.compound.size() > 0 && data.hasKey("name")) {
		eventNames.push_back(data.at("name"));
	}
	if (data.array.size() > 0) {
		for (std::list<Data>::const_iterator arrIter = data.array.begin(); arrIter != data.array.end(); arrIter++) {
			std::list<std::string> nested = getEventNames(*arrIter);
			eventNames.insert(eventNames.end(), nested.begin(), nested.end());
		}
	}
	if (data.compound.size() > 0) {
		for (std::map<std::string, Data>::const_iterator compIter = data.compound.begin(); compIter != data.compound.end(); compIter++) {
			std::list<std::string> nested = getEventNames(compIter->second);
			eventNames.insert(eventNames.end(), nested.begin(), nested.end());
		}
	}

	return eventNames;
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


void ChartToPromela::writeProgram(std::ostream& stream) {

	_traceTransitions = envVarIsTrue("USCXML_PROMELA_TRANSITION_TRACE");
	_writeTransitionPrintfs = envVarIsTrue("USCXML_PROMELA_TRANSITION_DEBUG");
	
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
	writeStrings(stream);
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
	writeDeclarations(stream);
	stream << std::endl;

	for (std::map<Arabica::DOM::Node<std::string>, ChartToPromela*>::iterator nestedIter = _machines.begin(); nestedIter != _machines.end(); nestedIter++) {
		nestedIter->second->writeDeclarations(stream);
		stream << std::endl;
	}

	stream << std::endl << "/* global inline functions */" << std::endl;

    if (_analyzer->usesComplexEventStruct()) {
        stream << "hidden _event_t tmpE;" << std::endl;
    } else {
        stream << "hidden int tmpE;" << std::endl;
    }
    stream << "hidden int tmpIndex;" << std::endl;

    
#if NEW_DELAY_RESHUFFLE
    if (_analyzer->usesEventField("delay")) {
        writeInsertWithDelay(stream);
        stream << std::endl;
    }
#endif
	
	if (_analyzer->usesEventField("delay") && _machines.size() > 0) {
        writeDetermineShortestDelay(stream);
		stream << std::endl;
		writeAdvanceTime(stream);
		stream << std::endl;
		writeRescheduleProcess(stream);
		stream << std::endl;
		writeScheduleMachines(stream);
		stream << std::endl;
	}

	{
		NodeSet<std::string> cancels = filterChildElements(_nsInfo.xmlNSPrefix + "cancel", _scxml, true);
		if (cancels.size() > 0) {
			writeCancelEvents(stream);
			stream << std::endl;
		}
	}
	{
		NodeSet<std::string> invokes = filterChildElements(_nsInfo.xmlNSPrefix + "invoke", _scxml, true);
		if (invokes.size() > 0 && _analyzer->usesEventField("delay")) {
			writeRemovePendingEventsFromInvoker(stream);
			stream << std::endl;
		}

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