/**
 *  @file
 *  @author     2012-2014 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#ifndef CHARTTOFSM_H_IOKPYEBY
#define CHARTTOFSM_H_IOKPYEBY

#include "uscxml/DOMUtils.h"
#include "uscxml/interpreter/InterpreterDraft6.h"
#include <DOM/Document.hpp>
#include <DOM/Node.hpp>
#include <XPath/XPath.hpp>
#include <ostream>
#include <list>

namespace uscxml {
class GlobalState;
class GlobalTransition;

class USCXML_API GlobalState {
public:

	GlobalState() {}
	GlobalState(const Arabica::XPath::NodeSet<std::string>& activeStates,
	            const Arabica::XPath::NodeSet<std::string>& alreadyEnteredStates, // we need to remember for binding=late
	            const std::map<std::string, Arabica::XPath::NodeSet<std::string> >& historyStates);

	Arabica::XPath::NodeSet<std::string> activeStates;
	Arabica::XPath::NodeSet<std::string> alreadyEnteredStates;
	std::map<std::string, Arabica::XPath::NodeSet<std::string> > historyStates;

	std::map<std::string, GlobalTransition*> incoming;
	std::map<std::string, GlobalTransition*> outgoing;
	std::string stateId;

	bool isFinal;
};


class USCXML_API GlobalTransition {
public:
	class Action {
	public:
		Arabica::DOM::Node<std::string> onEntry;
		Arabica::DOM::Node<std::string> onExit;
		Arabica::DOM::Node<std::string> transition;
		Arabica::DOM::Node<std::string> entered;
		Arabica::DOM::Node<std::string> exited;
		Arabica::DOM::Node<std::string> invoke;
		Arabica::DOM::Node<std::string> uninvoke;
	};

	GlobalTransition(const Arabica::XPath::NodeSet<std::string>& transitions, DataModel dataModel);

	bool isValid; // constructor will determine, calling code will delete if not
	bool isEventless; // whether or not all our transitions are eventless
	bool isTargetless; // whether or not all our transitions are eventless
	bool isSubset; // there is a superset to this set

	std::vector<long> firstElemPerLevel;
	std::vector<long> nrElemPerLevel;
	std::vector<long> prioPerLevel;

	Arabica::XPath::NodeSet<std::string> transitions; // constituting transitions

	std::list<std::string> eventNames; // the list of longest event names that will enable this set
	std::string eventDesc; // space-seperated eventnames for convenience
	std::string condition; // conjunction of all the set's conditions

	// executable content we gathered when we took the transition
	std::list<Action> actions;

	Arabica::XPath::NodeSet<std::string> entered;
	Arabica::XPath::NodeSet<std::string> exited;

	Arabica::XPath::NodeSet<std::string> invoke;
	Arabica::XPath::NodeSet<std::string> uninvoke;

	std::string transitionId;
	std::string source;
	std::string destination;

protected:
	std::list<std::string> getCommonEvents(const Arabica::XPath::NodeSet<std::string>& transitions);
};

class USCXML_API FlatteningInterpreter : public InterpreterDraft6, public InterpreterMonitor {
public:
	FlatteningInterpreter(const Arabica::DOM::Document<std::string>& doc);
	virtual ~FlatteningInterpreter();

	Arabica::DOM::Document<std::string> getDocument() const; // overwrite to return flat FSM
	InterpreterState interpret();

protected:
	// gather executable content per microstep
	void executeContent(const Arabica::DOM::Element<std::string>& content, bool rethrow = false);

	// invoke and uninvoke
	virtual void invoke(const Arabica::DOM::Node<std::string>& element);
	virtual void cancelInvoke(const Arabica::DOM::Node<std::string>& element);

	// override to do nothing
	void send(const Arabica::DOM::Node<std::string>& element) {}
	void internalDoneSend(const Arabica::DOM::Element<std::string>& state);

	// InterpreterMonitor
	virtual void beforeMicroStep(Interpreter interpreter);
	virtual void onStableConfiguration(Interpreter interpreter);
	virtual void beforeExitingState(Interpreter interpreter, const Arabica::DOM::Element<std::string>& state, bool moreComing);
	virtual void beforeEnteringState(Interpreter interpreter, const Arabica::DOM::Element<std::string>& state, bool moreComing);
	virtual void beforeTakingTransition(Interpreter interpreter, const Arabica::DOM::Element<std::string>& transition, bool moreComing);

	void explode();
	void labelTransitions();
	void weightTransitions();
	void createDocument();

	Arabica::DOM::Node<std::string> globalStateToNode(GlobalState* globalState);
	Arabica::DOM::Node<std::string> globalTransitionToNode(GlobalTransition* globalTransition);

	GlobalState* _start;
	GlobalTransition* _currGlobalTransition;

	uint64_t _perfProcessed;
	uint64_t _perfTotal;
	uint64_t _lastTimeStamp;

	int maxDepth;
	int maxOrder;

	Arabica::DOM::Document<std::string> _flatDoc;
	std::map<std::string, GlobalState*> _globalConf;
};

class USCXML_API ChartToFSM {
public:
	static Interpreter flatten(const Interpreter& other);
	static uint64_t stateMachineComplexity(const Arabica::DOM::Element<std::string>& root);

protected:
	class USCXML_API Complexity {
	public:
		Complexity() : value(0) {}
		Complexity(uint64_t value) : value(value) {}

		Complexity& operator+=(const Complexity& rhs) {
			value += rhs.value;
			history.insert(history.end(), rhs.history.begin(), rhs.history.end());
			return *this;
		}

		Complexity& operator*=(const Complexity& rhs) {
			value *= rhs.value;
			history.insert(history.end(), rhs.history.begin(), rhs.history.end());
			return *this;
		}

		uint64_t value;
		std::list<uint64_t> history;
	};

	static Complexity calculateStateMachineComplexity(const Arabica::DOM::Element<std::string>& root);

};

}

#endif /* end of include guard: CHARTTOFSM_H_IOKPYEBY */
