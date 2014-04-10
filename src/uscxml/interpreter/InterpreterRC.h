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

#ifndef INTERPRETERRC_H_WLJEI019
#define INTERPRETERRC_H_WLJEI019

#include "uscxml/Interpreter.h"

namespace uscxml {

class InterpreterRC : public InterpreterImpl {
	void interpret();
	void mainEventLoop();
	void exitInterpreter();

	void microstep(const Arabica::XPath::NodeSet<std::string>& enabledTransitions);

	Arabica::XPath::NodeSet<std::string> selectEventlessTransitions();
	Arabica::XPath::NodeSet<std::string> selectTransitions(const std::string& event);
	bool isEnabledTransition(const Arabica::DOM::Node<std::string>& transition, const std::string& event);
	bool hasIntersection(const Arabica::XPath::NodeSet<std::string>& nodeSet1, const Arabica::XPath::NodeSet<std::string>& nodeSet2);

	void enterStates(const Arabica::XPath::NodeSet<std::string>& enabledTransitions);
	void exitStates(const Arabica::XPath::NodeSet<std::string>& enabledTransitions);

	Arabica::XPath::NodeSet<std::string> computeExitSet(const Arabica::XPath::NodeSet<std::string>& transitions);
	Arabica::XPath::NodeSet<std::string> computeExitSet(const Arabica::DOM::Node<std::string>& transition);

	void computeEntrySet(const Arabica::XPath::NodeSet<std::string>& transitions,
											 Arabica::XPath::NodeSet<std::string>& statesToEnter,
											 Arabica::XPath::NodeSet<std::string>& statesForDefaultEntry,
											 std::map<std::string, Arabica::DOM::Node<std::string> > defaultHistoryContent);
	void computeEntrySet(const Arabica::DOM::Node<std::string>& transition,
											 Arabica::XPath::NodeSet<std::string>& statesToEnter,
											 Arabica::XPath::NodeSet<std::string>& statesForDefaultEntry,
											 std::map<std::string, Arabica::DOM::Node<std::string> > defaultHistoryContent);

	Arabica::XPath::NodeSet<std::string> removeConflictingTransitions(const Arabica::XPath::NodeSet<std::string>& enabledTransitions);
	Arabica::DOM::Node<std::string> getTransitionDomain(const Arabica::DOM::Node<std::string>& transition);

	void addDescendantStatesToEnter(const Arabica::DOM::Node<std::string>& state,
																	Arabica::XPath::NodeSet<std::string>& statesToEnter,
																	Arabica::XPath::NodeSet<std::string>& statesForDefaultEntry,
																	std::map<std::string, Arabica::DOM::Node<std::string> > defaultHistoryContent);

	void addAncestorStatesToEnter(const Arabica::DOM::Node<std::string>& state,
																const Arabica::DOM::Node<std::string>& ancestor,
																Arabica::XPath::NodeSet<std::string>& statesToEnter,
																Arabica::XPath::NodeSet<std::string>& statesForDefaultEntry,
																std::map<std::string, Arabica::DOM::Node<std::string> > defaultHistoryContent);

	bool isInFinalState(const Arabica::DOM::Node<std::string>& state);
	Arabica::DOM::Node<std::string> findLCCA(const Arabica::XPath::NodeSet<std::string>& states);

	Arabica::XPath::NodeSet<std::string> getProperAncestors(const Arabica::DOM::Node<std::string>& s1,
																													const Arabica::DOM::Node<std::string>& s2);

	Arabica::XPath::NodeSet<std::string> getTargetStates(const Arabica::DOM::Node<std::string>& transition);

#if 0
	bool isDescendant(const Arabica::DOM::Node<std::string>& state1, const Arabica::DOM::Node<std::string>& state2);
	Arabica::XPath::NodeSet<std::string> getChildStates(const Arabica::DOM::Node<std::string>& state);
#endif

};

}

#endif /* end of include guard: INTERPRETERRC_H_WLJEI019 */
