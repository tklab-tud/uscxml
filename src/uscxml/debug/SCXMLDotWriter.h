/**
 *  @file
 *  @author     2012-2013 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#ifndef SCXMLDOTWRITER_H_AOP0OHXX
#define SCXMLDOTWRITER_H_AOP0OHXX

#include "uscxml/Interpreter.h"
#include <DOM/Document.hpp>
#include <XPath/XPath.hpp>
#include <fstream>
#include <set>

#undef max
#include <limits>

namespace uscxml {

class Interpreter;



/**
 * This writer, added as a monitor will output .dot files.
 *
 * # create a set of pdfs form the dot files
 * $ dot -Tpdf -O *.dot
 *     or
 * $ find . -name "*.dot" -exec dot -Tpdf -O {} \;
 *
 * # create a movie from the pdfs
 * $ dot -Tgif -O *.dot
 *     or
 * $ find . -name "*.dot" -exec dot -Tgif -O {} \;
 *
 * $ ffmpeg -r 3 -i <NAME>.%06d.dot.gif -r 25 movie.mpg
 * $ convert -delay 20 *.gif animated.gif
 *
 * # unflatten can be used to create more compact graphs
 * find . -name "*.dot" -exec unflatten -f -l2 -o {}.flat.dot {} \;
 */
class USCXML_API SCXMLDotWriter : public InterpreterMonitor {
public:

	struct StateAnchor {
		StateAnchor() : depth(std::numeric_limits<int32_t>::max()) {}
		Arabica::DOM::Element<std::string> element;
		uint32_t depth;
	};

	struct ElemDetails {
		std::string name;
		std::string details;
		std::string content;
	};

	struct DotState {
		DotState() : isBorder(false) {}
		Arabica::DOM::Element<std::string> node;
		std::multimap<std::string, Arabica::DOM::Element<std::string> > targets; // key is remote node, transition is element
		std::multimap<std::string, Arabica::DOM::Element<std::string> > events; // key is event name, value is transitions that react

		bool isBorder;
		std::set<std::string> childs;
		std::set<std::string> initialchilds;
		typedef std::multimap<std::string, Arabica::DOM::Element<std::string> > mmap_s_e_t;
	};

	SCXMLDotWriter();
	~SCXMLDotWriter();

	virtual void onStableConfiguration(Interpreter interpreter);
	virtual void afterCompletion(Interpreter interpreter);
	virtual void beforeTakingTransition(Interpreter interpreter, const Arabica::DOM::Element<std::string>& transition, bool moreComing);
	virtual void beforeMicroStep(Interpreter interpreter);

	static void toDot(const std::string& filename,
	                  Interpreter interpreter,
	                  const Arabica::DOM::Element<std::string>& transition = Arabica::DOM::Element<std::string>()) {
		std::list<SCXMLDotWriter::StateAnchor> emptyAnchors = std::list<SCXMLDotWriter::StateAnchor>();
		toDot(filename, interpreter, emptyAnchors, transition);
	}


	static void toDot(const std::string& filename,
	                  Interpreter interpreter,
	                  const std::list<SCXMLDotWriter::StateAnchor>& stateAnchors,
	                  const Arabica::DOM::Element<std::string>& transition = Arabica::DOM::Element<std::string>());

	void writeTo(std::ostream& os);

	std::string getDetailedLabel(const Arabica::DOM::Element<std::string>& elem, int indentation = 0);
	std::string colorForIndent(int indent);

	std::string idForNode(const Arabica::DOM::Node<std::string>& node);
	std::string nameForNode(const Arabica::DOM::Node<std::string>& node);
	std::string getPrefix();

	static std::string dotEscape(const std::string& text);
	static std::string portEscape(const std::string& text);

protected:

	SCXMLDotWriter(Interpreter interpreter,
	               const std::list<SCXMLDotWriter::StateAnchor>& stateAnchors,
	               const Arabica::DOM::Element<std::string>& transition);

	void assembleGraph(const Arabica::DOM::Element<std::string>& start, uint32_t depth = std::numeric_limits<int32_t>::max());
	void writeStateElement(std::ostream& os, const DotState& elem);
	void writeUnknownNode(std::ostream& os, const std::string& targetId);

	int _iteration;
	std::set<std::string> _knownIds;
	std::set<std::string> _unknownNodes;
	int _indentation;

	std::map<std::string, DotState> _graph;

	// these are only set in ephemeral instances per monitor call
	Arabica::DOM::Element<std::string> _transition;
	Interpreter _interpreter;
	std::string _xmlNSPrefix;
	std::list<StateAnchor> _anchors;
	std::map<std::string, std::string> _histories;
};

}

#endif /* end of include guard: SCXMLDOTWRITER_H_AOP0OHXX */
