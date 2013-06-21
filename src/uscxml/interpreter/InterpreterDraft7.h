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
