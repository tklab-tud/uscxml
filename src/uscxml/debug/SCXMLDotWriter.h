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

	struct ElemDetails {
		std::string name;
		std::string details;
		std::string content;
	};

	SCXMLDotWriter();
	~SCXMLDotWriter();

	virtual void onStableConfiguration(Interpreter interpreter);
	virtual void afterCompletion(Interpreter interpreter);
	virtual void beforeTakingTransitions(Interpreter interpreter, const Arabica::XPath::NodeSet<std::string>& transitions);
	virtual void beforeMicroStep(Interpreter interpreter);

	static void toDot(const std::string& filename,
	                  Interpreter interpreter,
	                  const Arabica::XPath::NodeSet<std::string>& transitions = Arabica::XPath::NodeSet<std::string>());

	std::string getDetailedLabel(const Arabica::DOM::Element<std::string>& elem, int indentation = 0);
	std::string colorForIndent(int indent);

	std::string idForNode(const Arabica::DOM::Node<std::string>& node);
	std::string nameForNode(const Arabica::DOM::Node<std::string>& node);
	std::string getPrefix();

	static std::string dotEscape(const std::string& text);

protected:

	SCXMLDotWriter(Interpreter interpreter,
	               const Arabica::XPath::NodeSet<std::string>& transitions);

	void writeSCXMLElement(std::ostream& os, const Arabica::DOM::Element<std::string>& elem);
	void writeStateElement(std::ostream& os, const Arabica::DOM::Element<std::string>& elem);
	void writeTransitionElement(std::ostream& os, const Arabica::DOM::Element<std::string>& elem);

	int _iteration;
	std::set<std::string> _knownIds;
	int _indentation;

	// these are only set in ephemeral instances per monitor call
	Arabica::XPath::NodeSet<std::string> _transitions;
	Interpreter _interpreter;
};

}

#endif /* end of include guard: SCXMLDOTWRITER_H_AOP0OHXX */
