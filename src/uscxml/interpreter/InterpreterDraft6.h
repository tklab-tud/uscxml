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

#ifndef INTERPRETERDRAFT6_H_JAXK9FE1
#define INTERPRETERDRAFT6_H_JAXK9FE1

#include "uscxml/Interpreter.h"

namespace uscxml {

class USCXML_API InterpreterDraft6 : public InterpreterImpl {
public:
	virtual ~InterpreterDraft6() {};

protected:

	void enterStates(const Arabica::XPath::NodeSet<std::string>& enabledTransitions);
	void addStatesToEnter(const Arabica::DOM::Element<std::string>& state,
	                      Arabica::XPath::NodeSet<std::string>& statesToEnter,
	                      Arabica::XPath::NodeSet<std::string>& statesForDefaultEntry,
	                      Arabica::XPath::NodeSet<std::string>& defaultHistoryContent);

	void exitStates(const Arabica::XPath::NodeSet<std::string>& enabledTransitions);

	Arabica::XPath::NodeSet<std::string> removeConflictingTransitions(const Arabica::XPath::NodeSet<std::string>& enabledTransitions);
	bool isPreemptingTransition(const Arabica::DOM::Element<std::string>& t1, const Arabica::DOM::Element<std::string>& t2);

	bool isCrossingBounds(const Arabica::DOM::Element<std::string>& transition);
	bool isWithinParallel(const Arabica::DOM::Element<std::string>& transition);
	Arabica::DOM::Node<std::string> findLCPA(const Arabica::XPath::NodeSet<std::string>& states);

	std::map<Arabica::DOM::Element<std::string>, bool> _transWithinParallel; // this is costly to calculate

	virtual void handleDOMEvent(Arabica::DOM::Events::Event<std::string>& event);

};

}

#endif /* end of include guard: INTERPRETERDRAFT6_H_JAXK9FE1 */
