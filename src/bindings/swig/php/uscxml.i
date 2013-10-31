%module(directors="1", allprotected="1") uscxmlNativePHP

// import swig typemaps
%include "stl.i"

// macros from cmake
%import "uscxml/config.h"

// disable warning related to unknown base class
#pragma SWIG nowarn=401

%rename(c_array) array;
%rename(equals) operator==; 
%rename(isValid) operator bool;
%ignore operator!=;
%ignore operator<;
%ignore operator=;
%ignore operator[];
%ignore operator std::list<Data>;
%ignore operator std::string;
%ignore operator std::map<std::string,Data>;
%ignore operator<<;

%template(StringMap) std::map<std::string, std::string>;
%template(StringVector) std::vector<std::string>;
%template(Params) std::map<std::string, std::vector<std::string> >;

//**************************************************
// This ends up in the generated wrapper code
//**************************************************

%{
#include "../../../uscxml/Message.h"
#include "../../../uscxml/Interpreter.h"
#include "../../../uscxml/concurrency/BlockingQueue.h"
#include "../../../uscxml/DOMUtils.h"

using namespace uscxml;

%}

// Add this to the very top of the generated wrapper code

%insert("begin") %{
void*** tsrm_ls;
%}

%feature("director") uscxml::InterpreterMonitor;

%ignore uscxml::NumAttr;
%ignore uscxml::SCXMLParser;
%ignore uscxml::InterpreterImpl;

//***********************************************
// Beautify interpreter class
//***********************************************

%ignore uscxml::Interpreter::getDelayQueue();

%extend uscxml::Interpreter {
	std::vector<std::string> getConfiguration() {
		std::vector<std::string> config;
		Arabica::XPath::NodeSet<std::string> configNodes = self->getConfiguration();
		for (int i = 0; i < configNodes.size(); i++) {
			config.push_back(ATTR(configNodes[i], "id"));
		}
		return config;		
	}
}
%ignore uscxml::Interpreter::getConfiguration();

%extend uscxml::Interpreter {
	std::vector<std::string> getBasicConfiguration() {
		std::vector<std::string> config;
		Arabica::XPath::NodeSet<std::string> configNodes = self->getBasicConfiguration();
		for (int i = 0; i < configNodes.size(); i++) {
			config.push_back(ATTR(configNodes[i], "id"));
		}
		return config;		
	}
}
%ignore uscxml::Interpreter::getBasicConfiguration();

%extend uscxml::Interpreter {
	bool isState(const std::string stateId) {
		Arabica::DOM::Node<std::string> state = self->getState(stateId);
		return self->isState(state);
	}
}
%ignore uscxml::Interpreter::isState(Arabica::DOM::Node<std::string>);

%extend uscxml::Interpreter {
	bool isPseudoState(const std::string stateId) {
		Arabica::DOM::Node<std::string> state = self->getState(stateId);
		return self->isPseudoState(state);
	}
}
%ignore uscxml::Interpreter::isPseudoState(Arabica::DOM::Node<std::string>);

%extend uscxml::Interpreter {
	bool isTransitionTarget(const std::string stateId) {
		Arabica::DOM::Node<std::string> state = self->getState(stateId);
		return self->isTransitionTarget(state);
	}
}
%ignore uscxml::Interpreter::isTransitionTarget(Arabica::DOM::Node<std::string>);

%extend uscxml::Interpreter {
	bool isTargetless(const std::string stateId) {
		Arabica::DOM::Node<std::string> state = self->getState(stateId);
		return self->isTargetless(state);
	}
}
%ignore uscxml::Interpreter::isTargetless(Arabica::DOM::Node<std::string>);

%extend uscxml::Interpreter {
	bool isAtomic(const std::string stateId) {
		Arabica::DOM::Node<std::string> state = self->getState(stateId);
		return self->isAtomic(state);
	}
}
%ignore uscxml::Interpreter::isAtomic(Arabica::DOM::Node<std::string>);

%extend uscxml::Interpreter {
	bool isInitial(const std::string stateId) {
		Arabica::DOM::Node<std::string> state = self->getState(stateId);
		return self->isInitial(state);
	}
}
%ignore uscxml::Interpreter::isInitial(Arabica::DOM::Node<std::string>);

%extend uscxml::Interpreter {
	bool isFinal(const std::string stateId) {
		Arabica::DOM::Node<std::string> state = self->getState(stateId);
		return self->isFinal(state);
	}
}
%ignore uscxml::Interpreter::isFinal(Arabica::DOM::Node<std::string>);

%extend uscxml::Interpreter {
	bool isHistory(const std::string stateId) {
		Arabica::DOM::Node<std::string> state = self->getState(stateId);
		return self->isHistory(state);
	}
}
%ignore uscxml::Interpreter::isHistory(Arabica::DOM::Node<std::string>);

%extend uscxml::Interpreter {
	bool isParallel(const std::string stateId) {
		Arabica::DOM::Node<std::string> state = self->getState(stateId);
		return self->isParallel(state);
	}
}
%ignore uscxml::Interpreter::isParallel(Arabica::DOM::Node<std::string>);

%extend uscxml::Interpreter {
	bool isCompound(const std::string stateId) {
		Arabica::DOM::Node<std::string> state = self->getState(stateId);
		return self->isCompound(state);
	}
}
%ignore uscxml::Interpreter::isCompound(Arabica::DOM::Node<std::string>);

%extend uscxml::Interpreter {
	bool isDescendant(const std::string stateId1, const std::string stateId2) {
		Arabica::DOM::Node<std::string> state1 = self->getState(stateId1);
		Arabica::DOM::Node<std::string> state2 = self->getState(stateId2);
		return self->isDescendant(state1, state2);
	}
}
%ignore uscxml::Interpreter::isDescendant(Arabica::DOM::Node<std::string>);

//***********************************************
// Parse the header file to generate wrappers
//***********************************************

%include "../../../uscxml/Common.h"
%include "../../../uscxml/Message.h"
%include "../../../uscxml/Interpreter.h"
%include "../../../uscxml/concurrency/BlockingQueue.h"

%template(ParentQueue) uscxml::concurrency::BlockingQueue<uscxml::SendRequest>;
