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
	void enterStates(const Arabica::XPath::NodeSet<std::string>& enabledTransitions);
	void exitStates(const Arabica::XPath::NodeSet<std::string>& enabledTransitions);
	Arabica::XPath::NodeSet<std::string> removeConflictingTransitions(const Arabica::XPath::NodeSet<std::string>& enabledTransitions);

	bool hasIntersection(const Arabica::XPath::NodeSet<std::string>& nodeSet1, const Arabica::XPath::NodeSet<std::string>& nodeSet2);

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

	Arabica::DOM::Node<std::string> getTransitionDomain(const Arabica::DOM::Element<std::string>& transition);
	Arabica::XPath::NodeSet<std::string> getEffectiveTargetStates(const Arabica::DOM::Element<std::string>& transition);

	void addDescendantStatesToEnter(const Arabica::DOM::Element<std::string>& state,
	                                Arabica::XPath::NodeSet<std::string>& statesToEnter,
	                                Arabica::XPath::NodeSet<std::string>& statesForDefaultEntry,
	                                std::map<std::string, Arabica::DOM::Node<std::string> > defaultHistoryContent);

	void addAncestorStatesToEnter(const Arabica::DOM::Element<std::string>& state,
	                              const Arabica::DOM::Element<std::string>& ancestor,
	                              Arabica::XPath::NodeSet<std::string>& statesToEnter,
	                              Arabica::XPath::NodeSet<std::string>& statesForDefaultEntry,
	                              std::map<std::string, Arabica::DOM::Node<std::string> > defaultHistoryContent);

};

}

#endif /* end of include guard: INTERPRETERRC_H_WLJEI019 */
