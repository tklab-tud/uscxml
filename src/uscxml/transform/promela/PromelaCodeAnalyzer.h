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

#ifndef PROMELACODEANALYZER_H_E89FF519
#define PROMELACODEANALYZER_H_E89FF519

#include "uscxml/transform/Trie.h"
#include "uscxml/plugins/datamodel/promela/PromelaParser.h"
#include "uscxml/plugins/datamodel/promela/parser/promela.tab.hpp"

#include <set>

namespace uscxml {

class ChartToPromela;

class USCXML_API PromelaCodeAnalyzer {
public:
	class PromelaTypedef {
	public:
		PromelaTypedef() {}
		std::string name;
		std::string type;
		size_t arraySize = 0;
		int minValue = 0;
		int maxValue = 0;
		std::map<std::string, PromelaTypedef> types;
		std::set<ChartToPromela*> occurrences;

		bool operator==(const PromelaTypedef& other) const {
			return name == other.name;
		}

	};

	PromelaCodeAnalyzer() : _eventTrie(".") {}

	void analyze(ChartToPromela* interpreter);

	void addCode(const std::string& code, ChartToPromela* interpreter);
	void addLiteral(const std::string& stateName, int forceIndex = -1);

	bool usesComplexEventStruct() {
		return _typeDefs.types.find("_event") != _typeDefs.types.end() && _typeDefs.types["_event"].types.size() > 0;
	}
	bool usesEventField(const std::string& fieldName) {
		if (usesComplexEventStruct() && _typeDefs.types["_event"].types.find(fieldName) != _typeDefs.types["_event"].types.end())
			return true;
		return false;
	}
	bool usesCancel(const std::string& elementName) {
		return _usesCancel;
	}

	bool usesEventDataField(const std::string& fieldName) {
		if (usesComplexEventStruct() &&
		        _typeDefs.types["_event"].types.find("data") != _typeDefs.types["_event"].types.end() &&
		        _typeDefs.types["_event"].types["data"].types.find(fieldName) != _typeDefs.types["_event"].types["data"].types.end())
			return true;
		return false;
	}

	size_t largestDelay = 0;

	std::string getTypeAssignment(const std::string& varTo, const std::string& varFrom, const PromelaTypedef& type, size_t indent = 0);
	std::string getTypeReset(const std::string& var, const PromelaTypedef& type, size_t indent = 0);

	bool usesInPredicate() {
		return _usesInPredicate;
	}
	void usesInPredicate(bool value) {
		_usesInPredicate = value;
	}
	bool usesPlatformVars() {
		return _usesPlatformVars;
	}

	bool hasIndexLessLoops() {
		return _hasIndexLessLoops;
	}

	std::string macroForLiteral(const std::string& literal);
	int indexForLiteral(const std::string& literal);

	std::set<std::string> getLiterals() {
		return _literals;
	}
	std::set<std::string> getEventsWithPrefix(const std::string& prefix);

	Trie& getTrie() {
		return _eventTrie;
	}

	std::string adaptCode(const std::string& code, const std::string& prefix);

	static std::string prefixIdentifiers(const std::string& expr, const std::string& prefix);
	static std::list<std::pair<size_t, size_t> > getTokenPositions(const std::string& expr, int type, PromelaParserNode* ast);

	PromelaTypedef& getTypes() {
		return _typeDefs;
	}

	PromelaTypedef& getType(const std::string& typeName) {
		return _typeDefs.types.at(typeName);
	}

	std::string sanitizeCode(const std::string& code);
	void addEvent(const std::string& eventName);
	std::string createMacroName(const std::string& literal);

protected:
	void addState(const std::string& stateName, size_t index);

	int enumerateLiteral(const std::string& literal, int forceIndex = -1);

	std::map<std::string, std::string> _strMacros;  // macronames for string literals
	std::map<std::string, int> _strIndex;               // integer enumeration for string
	std::set<std::string> _literals;

	PromelaTypedef _typeDefs;
	Trie _eventTrie;

private:
	std::set<std::string> _macroNameSet; // helper set for uniqueness of macros
	int _lastStrIndex = 1;
	bool _usesCancel = false;
	bool _usesInPredicate = false;
	bool _usesPlatformVars = false;
	bool _hasIndexLessLoops = false;
};



}

#endif /* end of include guard: PROMELACODEANALYZER_H_E89FF519 */
