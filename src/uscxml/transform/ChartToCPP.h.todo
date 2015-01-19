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

#ifndef FSMTOCPP_H_201672B0
#define FSMTOCPP_H_201672B0

#include "uscxml/interpreter/InterpreterDraft6.h"
#include "uscxml/DOMUtils.h"
#include "uscxml/util/Trie.h"

#include <DOM/Document.hpp>
#include <DOM/Node.hpp>
#include <XPath/XPath.hpp>
#include <ostream>

namespace uscxml {

class USCXML_API ChartToCPP : public InterpreterDraft6 {
public:
	static void writeProgram(std::ostream& stream,
	                         const Interpreter& interpreter);

	static std::string beautifyIndentation(const std::string& code, int indent = 0);

protected:
	ChartToCPP();
	void writeProgram(std::ostream& stream);

	void initNodes();

	void writeEvents(std::ostream& stream);
	void writeStates(std::ostream& stream);
	void writeDeclarations(std::ostream& stream);
	void writeExecutableContent(std::ostream& stream, const Arabica::DOM::Element<std::string>& node, int indent = 0);
	void writeInlineComment(std::ostream& stream, const Arabica::DOM::Element<std::string>& node);
	void writeFSM(std::ostream& stream);
	void writeEventDispatching(std::ostream& stream);
	void writeMain(std::ostream& stream);

	void writeIfBlock(std::ostream& stream, const Arabica::XPath::NodeSet<std::string>& condChain, int indent = 0);
	void writeDispatchingBlock(std::ostream& stream, const Arabica::XPath::NodeSet<std::string>& transChain, int indent = 0);

	Arabica::XPath::NodeSet<std::string> getTransientContent(const Arabica::DOM::Element<std::string>& state);
	Arabica::DOM::Node<std::string> getUltimateTarget(const Arabica::DOM::Element<std::string>& transition);

	Trie _eventTrie;
	Arabica::XPath::NodeSet<std::string> _globalStates;
	Arabica::DOM::Element<std::string> _startState;
	std::map<std::string, Arabica::DOM::Element<std::string> > _states;
	std::map<Arabica::DOM::Element<std::string>, int> _transitions;

};

}

#endif /* end of include guard: FSMTOCPP_H_201672B0 */
