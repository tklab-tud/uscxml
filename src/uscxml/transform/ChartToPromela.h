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

#ifndef CHARTTOPROMELA_H_RP48RFDJ
#define CHARTTOPROMELA_H_RP48RFDJ

#include "Transformer.h"
#include "ChartToFSM.h"
#include "uscxml/interpreter/InterpreterDraft6.h"
#include "uscxml/DOMUtils.h"
#include "uscxml/util/Trie.h"

#include <DOM/Document.hpp>
#include <DOM/Node.hpp>
#include <XPath/XPath.hpp>
#include <ostream>

namespace uscxml {

class PromelaCodeAnalyzer;
class ChartToPromela;
class PromelaParserNode;
	
class USCXML_API PromelaInline {
public:
	PromelaInline() : type(PROMELA_NIL) {}

	operator bool() {
		return (type != PROMELA_NIL);
	}

	void dump();

	enum PromelaInlineType {
		PROMELA_NIL,
		PROMELA_CODE,
		PROMELA_EVENT_SOURCE,
		PROMELA_EVENT_SOURCE_CUSTOM,
		PROMELA_PROGRESS_LABEL,
		PROMELA_ACCEPT_LABEL,
		PROMELA_END_LABEL
	};

	std::string content;
	PromelaInlineType type;
};

class USCXML_API PromelaEventSource {
public:
	
	enum PromelaEventSourceType {
		PROMELA_EVENT_SOURCE_INVALID,
		PROMELA_EVENT_SOURCE_INVOKER,
		PROMELA_EVENT_SOURCE_GLOBAL,
	};
	
	PromelaEventSource();
	PromelaEventSource(const PromelaInline& source, PromelaCodeAnalyzer* analyzer = NULL, uint32_t externalQueueLength = 0);
	
	void writeStart(std::ostream& stream, int indent = 0);
	void writeStop(std::ostream& stream, int indent = 0);
	void writeDeclarations(std::ostream& stream, int indent = 0);
	void writeBody(std::ostream& stream);
	
	operator bool() {
		return type != PROMELA_EVENT_SOURCE_INVALID;
	}
	
	PromelaInline source;
	std::string name;
	uint32_t externalQueueLength;
	uint32_t longestSequence;
	
	Arabica::DOM::Node<std::string> container;
	std::list<std::list<std::string> > sequences;
	PromelaEventSourceType type;
	PromelaCodeAnalyzer* analyzer;
};

class USCXML_API PromelaInlines {
public:
	
	static PromelaInlines fromNodeSet(const Arabica::XPath::NodeSet<std::string>& node, bool recurse = false);
	static PromelaInlines fromNode(const Arabica::DOM::Node<std::string>& node);
	static PromelaInlines fromString(const std::string& text);
	
	PromelaInlines(const std::string& text, const Arabica::DOM::Node<std::string>& node);
	PromelaInlines();

	void merge(const PromelaInlines& other) {
		code.insert(code.end(), other.code.begin(), other.code.end());
		nrProgressLabels += other.nrProgressLabels;
		nrAcceptLabels += other.nrAcceptLabels;
		nrEndLabels += other.nrEndLabels;
		nrEventSources += other.nrEventSources;
		nrCodes += other.nrCodes;
	}

	operator bool() {
		return code.size() > 0;
	}

	std::list<PromelaInline> code;
	int nrProgressLabels;
	int nrAcceptLabels;
	int nrEndLabels;
	int nrEventSources;
	int nrCodes;
};

class USCXML_API PromelaCodeAnalyzer {
public:
	class PromelaTypedef {
	public:
		PromelaTypedef() : arraySize(0), minValue(0), maxValue(0) {}
		std::string name;
		std::string type;
		size_t arraySize;
		size_t minValue;
		size_t maxValue;
		std::map<std::string, PromelaTypedef> types;
		std::set<ChartToPromela*> occurrences;
		
		bool operator==(const PromelaTypedef& other) const {
			return name == other.name;
		}

	};

	PromelaCodeAnalyzer() : _eventTrie("."), _lastStrIndex(1), _lastStateIndex(0), _lastEventIndex(1), _usesInPredicate(false), _usesPlatformVars(false) {
	}

	void addCode(const std::string& code, ChartToPromela* interpreter);
	void addEvent(const std::string& eventName);
	void addState(const std::string& stateName);
	void addOrigState(const std::string& stateName);
	void addLiteral(const std::string& stateName, int forceIndex = -1);

	bool usesComplexEventStruct() {
		return _typeDefs.types.find("_event") != _typeDefs.types.end() && _typeDefs.types["_event"].types.size() > 0;
	}
	bool usesEventField(const std::string& fieldName) {
		if (usesComplexEventStruct() && _typeDefs.types["_event"].types.find(fieldName) != _typeDefs.types["_event"].types.end())
			return true;
		return false;
	}

	bool usesEventDataField(const std::string& fieldName) {
		if (usesComplexEventStruct() &&
				_typeDefs.types["_event"].types.find("data") != _typeDefs.types["_event"].types.end() &&
				_typeDefs.types["_event"].types["data"].types.find(fieldName) != _typeDefs.types["_event"].types["data"].types.end())
			return true;
		return false;
	}

	bool usesInPredicate() {
		return _usesInPredicate;
	}
	bool usesPlatformVars() {
		return _usesPlatformVars;
	}

	std::string macroForLiteral(const std::string& literal);
	int indexForLiteral(const std::string& literal);

	std::set<std::string> getLiterals() {
		return _strLiterals;
	}
	std::set<std::string> getEventsWithPrefix(const std::string& prefix);
	std::map<std::string, int>& getEvents() {
		return _events;
	}

	std::map<std::string, int>& getStates() {
		return _states;
	}

	std::map<std::string, int>& getOrigStates() {
		return _origStateIndex;
	}


	Trie& getTrie() {
		return _eventTrie;
	}

	std::string adaptCode(const std::string& code, const std::string& prefix);

	static std::string prefixIdentifiers(const std::string& expr, const std::string& prefix);
	static std::list<std::pair<size_t, size_t> > getTokenPositions(const std::string& expr, int type, PromelaParserNode* ast);

	PromelaTypedef& getTypes() {
		return _typeDefs;
	}

protected:
	std::string createMacroName(const std::string& literal);
	int enumerateLiteral(const std::string& literal, int forceIndex = -1);

	std::set<std::string> _strLiterals;                 // all string literals
	std::map<std::string, std::string> _strMacroNames;  // macronames for string literals
	std::map<std::string, int> _strIndex;               // integer enumeration for string
	std::map<std::string, int> _origStateIndex;         // state enumeration for original states

	std::map<std::string, int> _states;
	std::map<std::string, int> _events;
	
	PromelaTypedef _typeDefs;
	Trie _eventTrie;

private:
	std::set<std::string> _macroNameSet; // helper set for uniqueness of macros
	int _lastStrIndex;
	int _lastStateIndex;
	int _lastEventIndex;
	bool _usesInPredicate;
	bool _usesPlatformVars;
};

class ExecContentSeqItem {
public:
	enum ExecContentType {
		EXEC_CONTENT_ALL_BUT,
		EXEC_CONTENT_ONLY_FOR,
		EXEC_CONTENT_EVERY
	};

	ExecContentSeqItem(ExecContentType type, const std::set<GlobalTransition*>& transitions, const GlobalTransition::Action& action)
	: type(type), transitions(transitions), action(action) {}
	ExecContentSeqItem(ExecContentType type, GlobalTransition* transition, const GlobalTransition::Action& action)
	: type(type), action(action) {
		transitions.insert(transition);
	}
	
	ExecContentType type;
	std::set<GlobalTransition*> transitions;
	GlobalTransition::Action action;
};

class HistoryTransitionClass {
public:
	HistoryTransitionClass(GlobalTransition* transition);
	HistoryTransitionClass(const std::string& from, const std::string& to);
	
	void init(const std::string& from, const std::string& to);
	
	std::map<std::string, std::set<std::string> > toRemember;
	std::map<std::string, std::set<std::string> > toKeep;
	std::map<std::string, std::set<std::string> > toForget;
	
	std::set<GlobalTransition*> members;


	void merge(const HistoryTransitionClass& other);
	bool matches(const HistoryTransitionClass& other);
};
	
class USCXML_API ChartToPromela : public TransformerImpl, public ChartToFSM {
public:

	virtual ~ChartToPromela();
	static Transformer transform(const Interpreter& other);
	
	void writeTo(std::ostream& stream);
	
protected:
	ChartToPromela(const Interpreter& other) : TransformerImpl(), ChartToFSM(other), _analyzer(NULL), _machinesAll(NULL), _parent(NULL), _parentTopMost(NULL), _machinesAllPerId(NULL) {}

	void initNodes();

	static std::string beautifyIndentation(const std::string& code, int indent = 0);

	void writeProgram(std::ostream& stream);

	void writeEvents(std::ostream& stream);
	void writeStates(std::ostream& stream);
	void writeStateMap(std::ostream& stream);
	void writeHistoryArrays(std::ostream& stream);
	void writeTypeDefs(std::ostream& stream);
	void writeStrings(std::ostream& stream);
	void writeDeclarations(std::ostream& stream);
	void writeEventSources(std::ostream& stream);
	void writeTransition(std::ostream& stream, GlobalTransition* transition, int indent = 0);
	std::string conditionalizeForHist(const std::set<GlobalTransition*>& transitions, int indent = 0);
	std::string conditionalizeForHist(GlobalTransition* transition, int indent = 0);
	void writeHistoryAssignments(std::ostream& stream, GlobalTransition* transition, int indent = 0);
	void writeTransitionClosure(std::ostream& stream, GlobalTransition* transition, GlobalState* state, int indent = 0);

	void writeExecutableContent(std::ostream& stream, const Arabica::DOM::Node<std::string>& node, int indent = 0);
	void writeInlineComment(std::ostream& stream, const Arabica::DOM::Node<std::string>& node);
	void writeFSM(std::ostream& stream);
	void writeEventDispatching(std::ostream& stream);
	void writeMain(std::ostream& stream);

	void writeIfBlock(std::ostream& stream, const Arabica::XPath::NodeSet<std::string>& condChain, int indent = 0);
	void writeDispatchingBlock(std::ostream& stream, std::list<GlobalTransition*>, int indent = 0);

	void writeStartInvoker(std::ostream& stream, const Arabica::DOM::Node<std::string>& node, ChartToPromela* invoker, int indent = 0);
	void writeRemovePendingEventsFromInvoker(std::ostream& stream, ChartToPromela* invoker, int indent = 0, bool atomic = true);
	void writeCancelWithIdOrExpr(std::ostream& stream, const Arabica::DOM::Element<std::string>& cancel, ChartToPromela* invoker, int indent = 0);
	
	Arabica::XPath::NodeSet<std::string> getTransientContent(const Arabica::DOM::Element<std::string>& state, const std::string& source = "");
	//Arabica::DOM::Node<std::string> getUltimateTarget(const Arabica::DOM::Element<std::string>& transition);
	
	static std::string declForRange(const std::string& identifier, long minValue, long maxValue, bool nativeOnly = false);
	static std::string conditionForHistoryTransition(const GlobalTransition* transition);

//	std::string replaceStringsInExpression(const std::string& expr);

	std::string sanitizeCode(const std::string& code);
	std::string dataToAssignments(const std::string& prefix, const Data& data);
	
//	Arabica::XPath::NodeSet<std::string> _globalStates;
//	Arabica::DOM::Node<std::string> _startState;
//	std::map<std::string, Arabica::DOM::Element<std::string> > _states;
//	std::map<Arabica::DOM::Element<std::string>, int> _transitions;

	std::list<std::string> _varInitializers; // pending initializations for arrays

	PromelaCodeAnalyzer* _analyzer;

	uint32_t _externalQueueLength;
	uint32_t _internalQueueLength;
	
	std::map<std::string, PromelaEventSource> _invokers;
	PromelaEventSource _globalEventSource;
	
	std::map<std::string, std::map<std::string, size_t> > _historyMembers; // ids of all history states
	std::set<std::string> _dataModelVars;
	
	Arabica::DOM::Node<std::string> _finalize;
	std::map<Arabica::DOM::Node<std::string>, ChartToPromela*> _machines;
	std::map<Arabica::DOM::Node<std::string>, ChartToPromela*>* _machinesAll;
	ChartToPromela* _parent; // our invoking interpreter
	ChartToPromela* _parentTopMost;
	
	std::map<std::string, Arabica::DOM::Node<std::string> > _machinesPerId;
	std::map<std::string, Arabica::DOM::Node<std::string> >* _machinesAllPerId;
	std::string _prefix; // our prefix in case of nested SCXML documents
	std::string _invokerid;
	
	friend class PromelaEventSource;
};

}

#endif /* end of include guard: CHARTTOPROMELA_H_RP48RFDJ */
