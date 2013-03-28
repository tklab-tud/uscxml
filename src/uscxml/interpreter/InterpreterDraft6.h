#ifndef INTERPRETERDRAFT6_H_JAXK9FE1
#define INTERPRETERDRAFT6_H_JAXK9FE1

#include "uscxml/Interpreter.h"

namespace uscxml {

class InterpreterDraft6 : public Interpreter {
	void interpret();
	void mainEventLoop();
	
	void initializeData(const Arabica::DOM::Node<std::string>& data);
	void microstep(const Arabica::XPath::NodeSet<std::string>& enabledTransitions);
	void enterStates(const Arabica::XPath::NodeSet<std::string>& enabledTransitions);
	void addStatesToEnter(const Arabica::DOM::Node<std::string>& state,
	                      Arabica::XPath::NodeSet<std::string>& statesToEnter,
	                      Arabica::XPath::NodeSet<std::string>& statesForDefaultEntry);
	
	void exitStates(const Arabica::XPath::NodeSet<std::string>& enabledTransitions);
	void exitInterpreter();
	
	Arabica::XPath::NodeSet<std::string> selectEventlessTransitions();
	Arabica::XPath::NodeSet<std::string> selectTransitions(const std::string& event);
	Arabica::XPath::NodeSet<std::string> filterPreempted(const Arabica::XPath::NodeSet<std::string>& enabledTransitions);
	bool isPreemptingTransition(const Arabica::DOM::Node<std::string>& t1, const Arabica::DOM::Node<std::string>& t2);

};

}

#endif /* end of include guard: INTERPRETERDRAFT6_H_JAXK9FE1 */
