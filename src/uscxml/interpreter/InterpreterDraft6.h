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
	virtual InterpreterState interpret();
	virtual InterpreterState step(int blocking);
	void stabilize();

	void microstep(const Arabica::XPath::NodeSet<std::string>& enabledTransitions);
	void enterStates(const Arabica::XPath::NodeSet<std::string>& enabledTransitions);
	void addStatesToEnter(const Arabica::DOM::Node<std::string>& state,
	                      Arabica::XPath::NodeSet<std::string>& statesToEnter,
	                      Arabica::XPath::NodeSet<std::string>& statesForDefaultEntry,
	                      Arabica::XPath::NodeSet<std::string>& defaultHistoryContent);

	void exitStates(const Arabica::XPath::NodeSet<std::string>& enabledTransitions);
	void exitInterpreter();

	Arabica::XPath::NodeSet<std::string> selectEventlessTransitions();
	Arabica::XPath::NodeSet<std::string> selectTransitions(const std::string& event);
	Arabica::XPath::NodeSet<std::string> filterPreempted(const Arabica::XPath::NodeSet<std::string>& enabledTransitions);
	bool isPreemptingTransition(const Arabica::DOM::Node<std::string>& t1, const Arabica::DOM::Node<std::string>& t2);
	bool isEnabledTransition(const Arabica::DOM::Node<std::string>& transition, const std::string& event);

	Arabica::XPath::NodeSet<std::string> getDocumentInitialTransitions();

	bool isCrossingBounds(const Arabica::DOM::Node<std::string>& transition);
	bool isWithinParallel(const Arabica::DOM::Node<std::string>& transition);
	Arabica::DOM::Node<std::string> findLCPA(const Arabica::XPath::NodeSet<std::string>& states);

};

}

#endif /* end of include guard: INTERPRETERDRAFT6_H_JAXK9FE1 */
