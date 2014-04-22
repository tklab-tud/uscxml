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

#include "uscxml/DOMUtils.h"
#include "uscxml/util/Trie.h"

#include <DOM/Document.hpp>
#include <DOM/Node.hpp>
#include <XPath/XPath.hpp>
#include <ostream>

namespace uscxml {

class PromelaInline {
public:
	enum PromelaInlineType {
	    PROMELA_CODE,
	    PROMELA_EVENT_SOURCE,
	    PROMELA_PROGRESS_LABEL,
	    PROMELA_ACCEPT_LABEL,
	    PROMELA_END_LABEL
	};

	std::string content;
	PromelaInlineType type;
};

class PromelaInlines {
public:
	PromelaInlines() : hasProgressLabel(false), hasAcceptLabel(false), hasEndLabel(false), hasEventSource(false), hasCode(false) {}

	std::list<PromelaInline> inlines;
	bool hasProgressLabel;
	bool hasAcceptLabel;
	bool hasEndLabel;
	bool hasEventSource;
	bool hasCode;
};

struct PromelaEventSource {
	std::list<std::list<std::string> > sequences;
	void dump();
	operator bool() {
		return sequences.size() > 0;
	}
};

class FSMToPromela : public InterpreterDraft6 {
public:
	static void writeProgram(std::ostream& stream,
	                         const Interpreter& interpreter);
protected:
	FSMToPromela();
	void writeProgram(std::ostream& stream);

	void initNodes();

	void writeEvents(std::ostream& stream);
	void writeStates(std::ostream& stream);
	void writeDeclarations(std::ostream& stream);
	void writeEventSources(std::ostream& stream);
	void writeEventSource(std::ostream& stream, const std::string& name, const PromelaEventSource& source);
	void writeExecutableContent(std::ostream& stream, const Arabica::DOM::Node<std::string>& node, int indent = 0);
	void writeInlineComment(std::ostream& stream, const Arabica::DOM::Node<std::string>& node);
	void writeFSM(std::ostream& stream);
	void writeEventDispatching(std::ostream& stream);
	void writeMain(std::ostream& stream);


	void writeIfBlock(std::ostream& stream, const Arabica::XPath::NodeSet<std::string>& condChain, int indent = 0);
	void writeDispatchingBlock(std::ostream& stream, const Arabica::XPath::NodeSet<std::string>& transChain, int indent = 0);

	std::string beautifyIndentation(const std::string& code, int indent = 0);

	Arabica::XPath::NodeSet<std::string> getTransientContent(const Arabica::DOM::Node<std::string>& state);
	Arabica::DOM::Node<std::string> getUltimateTarget(const Arabica::DOM::Node<std::string>& transition);
	PromelaInlines getInlinePromela(const Arabica::XPath::NodeSet<std::string>& elements, bool recurse = false);

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
