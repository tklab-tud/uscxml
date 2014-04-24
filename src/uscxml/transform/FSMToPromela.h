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

#ifndef FSMTOPROMELA_H_RP48RFDJ
#define FSMTOPROMELA_H_RP48RFDJ

#include "uscxml/interpreter/InterpreterDraft6.h"
#include "uscxml/DOMUtils.h"
#include "uscxml/util/Trie.h"

#include <DOM/Document.hpp>
#include <DOM/Node.hpp>
#include <XPath/XPath.hpp>
#include <ostream>

namespace uscxml {

class PromelaInline {
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
	std::list<std::list<std::string> > sequences;

	PromelaInlineType type;
};

class PromelaInlines {
public:
	PromelaInlines() : progressLabels(0), acceptLabels(0), endLabels(0), eventSources(0), customEventSources(0), codes(0) {}

	void merge(const PromelaInlines& other) {
		inlines.insert(inlines.end(), other.inlines.begin(), other.inlines.end());
		progressLabels += other.progressLabels;
		acceptLabels += other.acceptLabels;
		endLabels += other.endLabels;
		eventSources += other.eventSources;
		customEventSources += other.customEventSources;
		codes += other.codes;
	}

	operator bool() {
		return inlines.size() > 0;
	}

	std::list<PromelaInline> inlines;
	int progressLabels;
	int acceptLabels;
	int endLabels;
	int eventSources;
	int customEventSources;
	int codes;
};

class PromelaEventSource {
public:

	enum PromelaEventSourceType {
	    PROMELA_EVENT_SOURCE_INVALID,
	    PROMELA_EVENT_SOURCE_INVOKER,
	    PROMELA_EVENT_SOURCE_GLOBAL,
	};

	PromelaEventSource();
	PromelaEventSource(const PromelaInlines& sources, const Arabica::DOM::Node<std::string>& parent);

	void writeStartEventSources(std::ostream& stream, int indent = 0);
	void writeStopEventSources(std::ostream& stream, int indent = 0);
	void writeDeclarations(std::ostream& stream, int indent = 0);
	void writeEventSource(std::ostream& stream);

	operator bool() {
		return type != PROMELA_EVENT_SOURCE_INVALID;
	}

	std::string name;
	PromelaInlines eventSources;
	Arabica::DOM::Node<std::string> container;
	PromelaEventSourceType type;
	Trie* trie;
};

class FSMToPromela : public InterpreterDraft6 {
public:
	static void writeProgram(std::ostream& stream,
	                         const Interpreter& interpreter);

	static std::string beautifyIndentation(const std::string& code, int indent = 0);

protected:
	FSMToPromela();
	void writeProgram(std::ostream& stream);

	void initNodes();

	void writeEvents(std::ostream& stream);
	void writeStates(std::ostream& stream);
	void writeDeclarations(std::ostream& stream);
	void writeEventSources(std::ostream& stream);
	void writeExecutableContent(std::ostream& stream, const Arabica::DOM::Node<std::string>& node, int indent = 0);
	void writeInlineComment(std::ostream& stream, const Arabica::DOM::Node<std::string>& node);
	void writeFSM(std::ostream& stream);
	void writeEventDispatching(std::ostream& stream);
	void writeMain(std::ostream& stream);

	void writeIfBlock(std::ostream& stream, const Arabica::XPath::NodeSet<std::string>& condChain, int indent = 0);
	void writeDispatchingBlock(std::ostream& stream, const Arabica::XPath::NodeSet<std::string>& transChain, int indent = 0);

	Arabica::XPath::NodeSet<std::string> getTransientContent(const Arabica::DOM::Node<std::string>& state);
	Arabica::DOM::Node<std::string> getUltimateTarget(const Arabica::DOM::Node<std::string>& transition);

	static PromelaInlines getInlinePromela(const std::string&);
	static PromelaInlines getInlinePromela(const Arabica::XPath::NodeSet<std::string>& elements, bool recurse = false);
	static PromelaInlines getInlinePromela(const Arabica::DOM::Node<std::string>& elements);

	Trie _eventTrie;
	Arabica::XPath::NodeSet<std::string> _globalStates;
	Arabica::DOM::Node<std::string> _startState;
	std::map<std::string, Arabica::DOM::Node<std::string> > _states;
	std::map<Arabica::DOM::Node<std::string>, int> _transitions;

	std::map<std::string, PromelaEventSource> _invokers;
	PromelaEventSource _globalEventSource;
};

}

#endif /* end of include guard: FSMTOPROMELA_H_RP48RFDJ */
