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

#ifndef INTERPRETERDRAFT7_H_WLJEI019
#define INTERPRETERDRAFT7_H_WLJEI019

#include "uscxml/Interpreter.h"

namespace uscxml {

class InterpreterDraft7 : public InterpreterImpl {
	void interpret();
	void mainEventLoop();
	void exitInterpreter();

	void microstep(const Arabica::XPath::NodeSet<std::string>& enabledTransitions);

	Arabica::XPath::NodeSet<std::string> selectEventlessTransitions();
	Arabica::XPath::NodeSet<std::string> selectTransitions(const std::string& event);

	void enterStates(const Arabica::XPath::NodeSet<std::string>& enabledTransitions);
	void exitStates(const Arabica::XPath::NodeSet<std::string>& enabledTransitions);

	Arabica::XPath::NodeSet<std::string> computeExitSet(const Arabica::XPath::NodeSet<std::string>& enabledTransitions,
	        const Arabica::XPath::NodeSet<std::string>& statesToExit);

	Arabica::XPath::NodeSet<std::string> computeEntrySet(const Arabica::XPath::NodeSet<std::string>& transitions,
	        const Arabica::XPath::NodeSet<std::string>& statesToEnter,
	        const Arabica::XPath::NodeSet<std::string>& statesForDefaultEntry);

	Arabica::XPath::NodeSet<std::string> removeConflictingTransitions(const Arabica::XPath::NodeSet<std::string>& enabledTransitions);
	Arabica::DOM::Node<std::string> getTransitionDomain(const Arabica::DOM::Node<std::string>& transition);

	Arabica::XPath::NodeSet<std::string> addDescendentStatesToEnter(const Arabica::DOM::Node<std::string>& state,
	        const Arabica::XPath::NodeSet<std::string>& statesToEnter,
	        const Arabica::XPath::NodeSet<std::string>& statesForDefaultEntry);

	Arabica::XPath::NodeSet<std::string> addAncestorsStatesToEnter(const Arabica::DOM::Node<std::string>& state,
	        const Arabica::DOM::Node<std::string>& ancestor,
	        const Arabica::XPath::NodeSet<std::string>& statesToEnter,
	        const Arabica::XPath::NodeSet<std::string>& statesForDefaultEntry);

};

}

#endif /* end of include guard: INTERPRETERDRAFT7_H_WLJEI019 */
