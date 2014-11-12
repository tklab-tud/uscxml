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
#include "uscxml/interpreter/InterpreterRC.h"
#include <DOM/Document.hpp>
#include <DOM/Node.hpp>
#include <XPath/XPath.hpp>
#include <ostream>
#include <list>

namespace uscxml {
class GlobalState;
class GlobalTransition;
class ChartToFSM;

class USCXML_API Complexity {
public:
	
	enum Variant {
		IGNORE_NOTHING,
		IGNORE_HISTORY,
		IGNORE_NESTED_DATA,
		IGNORE_HISTORY_AND_NESTED_DATA,
	};
	
	Complexity() : value(0), nestedData(0) {}
	Complexity(uint64_t value) : value(value), nestedData(0) {}
	
	Complexity& operator+=(const Complexity& rhs) {
		value += rhs.value;
		nestedData += rhs.nestedData;
		history.insert(history.end(), rhs.history.begin(), rhs.history.end());
		return *this;
	}
	
	Complexity& operator*=(const Complexity& rhs) {
		value *= rhs.value;
		nestedData += rhs.nestedData;
		history.insert(history.end(), rhs.history.begin(), rhs.history.end());
		return *this;
	}
	
	static uint64_t stateMachineComplexity(const Arabica::DOM::Element<std::string>& root, Complexity::Variant variant = IGNORE_NOTHING);

protected:
	static Complexity calculateStateMachineComplexity(const Arabica::DOM::Element<std::string>& root);

	uint64_t value;
	uint64_t nestedData;
	std::list<uint64_t> history;
};

class USCXML_API GlobalState {
public:

	GlobalState() {}
	GlobalState(const Arabica::XPath::NodeSet<std::string>& activeStates,
	            const Arabica::XPath::NodeSet<std::string>& alreadyEnteredStates, // we need to remember for binding=late
	            const std::map<std::string, Arabica::XPath::NodeSet<std::string> >& historyStates,
	            const std::string& xmlNSPrefix,
							ChartToFSM* flattener);

	std::set<int> activeStatesRefs;
	std::set<int> alreadyEnteredStatesRefs;
	std::map<std::string, std::set<int> > historyStatesRefs;
	
	Arabica::XPath::NodeSet<std::string> getActiveStates();
	Arabica::XPath::NodeSet<std::string> getAlreadyEnteredStates();
	std::map<std::string, Arabica::XPath::NodeSet<std::string> > getHistoryStates();
	
	std::list<GlobalTransition*> sortedOutgoing;
	std::string stateId;
	std::string activeId;

	long index;
	bool isFinal;
	
	ChartToFSM* interpreter;
};


class USCXML_API GlobalTransition {
public:
	class Action {
	public:
		bool operator<(const Action& other) const {
			if (onEntry < other.onEntry)
				return onEntry < other.onEntry;
			if (onExit < other.onExit)
				return onExit < other.onExit;
			if (transition < other.transition)
				return transition < other.transition;
			if (entered < other.entered)
				return entered < other.entered;
			if (exited < other.exited)
				return exited < other.exited;
			if (invoke < other.invoke)
				return invoke < other.invoke;
			if (uninvoke < other.uninvoke)
				return uninvoke < other.uninvoke;
			return false;
		}

		bool operator==(const Action& other) const {
			return !(other < *this) && !(*this < other);
		}
		bool operator!=(const Action& other) const {
			return !operator==(other);
		}
		
		typedef std::list<GlobalTransition::Action>::iterator iter_t;
		
		Arabica::DOM::Element<std::string> onEntry;
		Arabica::DOM::Element<std::string> onExit;
		Arabica::DOM::Element<std::string> transition;
		Arabica::DOM::Element<std::string> entered;
		Arabica::DOM::Element<std::string> exited;
		Arabica::DOM::Element<std::string> invoke;
		Arabica::DOM::Element<std::string> uninvoke;
		
	};

	GlobalTransition(const Arabica::XPath::NodeSet<std::string>& transitions, DataModel dataModel, ChartToFSM* flattener);
	static GlobalTransition* copyWithoutExecContent(GlobalTransition* other);
	
	bool isValid; // constructor will determine, calling code will delete if not
	bool isEventless; // whether or not all our transitions are eventless
	bool isTargetless; // whether or not all our transitions are eventless
	bool isSubset; // there is a superset to this set
	bool hasExecutableContent;
	
	uint32_t eventsRaised; // internal events this transition will raise
	uint32_t eventsSent; // external events this transition will send
	uint32_t eventsChainRaised; // maximum number of internal events raised when taking this transition in a chain
	uint32_t eventsChainSent; // maximum number of external events raised when taking this transition in a chain
	
	std::set<int> startTransitionRefs; // indices of eventful transitions that might trigger this transition
	
	std::set<int> transitionRefs; // indizes of constituting transitions
	Arabica::XPath::NodeSet<std::string> getTransitions() const;
	
	std::list<std::string> eventNames; // the list of longest event names that will enable this set
	std::string eventDesc; // space-seperated eventnames for convenience
	std::string condition; // conjunction of all the set's conditions
	std::string members; // a convenience string listing all constituting transitions

	// executable content we gathered when we took the transition
	std::list<Action> actions;

	std::string transitionId;
	std::string source;
	std::string destination;
	std::string activeDestination;

	GlobalTransition* historyBase; // we have a base transition that left our source with no history (-> we are a history transition)
	std::list<GlobalTransition*> historyTrans; // transitions from the same source but different histories
	std::set<std::string> histTargets; // constituting targets to history states

	long index;
	ChartToFSM* interpreter;

	bool operator< (const GlobalTransition& other) const;

protected:
	std::list<std::string> getCommonEvents(const Arabica::XPath::NodeSet<std::string>& transitions);
};


class USCXML_API ChartToFSM : public InterpreterRC, public InterpreterMonitor {
public:
	virtual ~ChartToFSM();

protected:
	ChartToFSM(const Interpreter& other);

	Arabica::DOM::Document<std::string> getDocument() const; // overwrite to return flat FSM
	InterpreterState interpret();
	
	Arabica::XPath::NodeSet<std::string> refsToStates(const std::set<int>&);
	Arabica::XPath::NodeSet<std::string> refsToTransitions(const std::set<int>&);
	
	std::vector<Arabica::DOM::Element<std::string> > indexedTransitions;
	std::vector<Arabica::DOM::Element<std::string> > indexedStates;

	// gather executable content per microstep
	void executeContent(const Arabica::DOM::Element<std::string>& content, bool rethrow = false);

	// invoke and uninvoke
	virtual void invoke(const Arabica::DOM::Element<std::string>& element);
	virtual void cancelInvoke(const Arabica::DOM::Element<std::string>& element);

	// override to do nothing
	void send(const Arabica::DOM::Element<std::string>& element) {}
	void internalDoneSend(const Arabica::DOM::Element<std::string>& state);

	// InterpreterMonitor
	virtual void beforeMicroStep(Interpreter interpreter);
	virtual void onStableConfiguration(Interpreter interpreter);
	virtual void beforeExitingState(Interpreter interpreter, const Arabica::DOM::Element<std::string>& state, bool moreComing);
	virtual void beforeEnteringState(Interpreter interpreter, const Arabica::DOM::Element<std::string>& state, bool moreComing);
	virtual void beforeTakingTransition(Interpreter interpreter, const Arabica::DOM::Element<std::string>& transition, bool moreComing);

	void explode();
	void getPotentialTransitionsForConf(const Arabica::XPath::NodeSet<std::string>& conf, std::map<std::string, GlobalTransition*>& outMap);
//	void labelTransitions();

	void indexTransitions(const Arabica::DOM::Element<std::string>& root);
	void annotateRaiseAndSend(const Arabica::DOM::Element<std::string>& root);
	bool hasForeachInBetween(const Arabica::DOM::Node<std::string>& ancestor, const Arabica::DOM::Node<std::string>& child);
	void updateRaisedAndSendChains(GlobalState* state, GlobalTransition* source, std::set<GlobalTransition*> visited);

	uint32_t getMinInternalQueueLength(uint32_t defaultVal);
	uint32_t getMinExternalQueueLength(uint32_t defaultVal);
	
	std::list<GlobalTransition*> sortTransitions(std::list<GlobalTransition*> list);

	// we need this static as we use it in a sort function
	static std::map<Arabica::DOM::Node<std::string>, Arabica::DOM::Node<std::string> > _transParents;
	
	static bool filterSameState(const Arabica::XPath::NodeSet<std::string>& transitions);

	uint64_t _perfTransProcessed;
	uint64_t _perfTransTotal;
	uint64_t _perfTransUsed;
	uint64_t _perfStatesProcessed;
	uint64_t _perfStatesSkippedProcessed;
	uint64_t _perfStatesSkippedTotal;
	uint64_t _perfStatesCachedProcessed;
	uint64_t _perfStatesCachedTotal;
	uint64_t _perfMicroStepProcessed;
	uint64_t _perfMicroStepTotal;
	uint64_t _lastTimeStamp;

	size_t _lastTransientStateId;
	size_t _lastStateIndex;
	size_t _lastTransIndex;

	bool _skipEventChainCalculations;
	size_t _maxEventSentChain;
	size_t _maxEventRaisedChain;
	size_t _doneEventRaiseTolerance;
	
	GlobalState* _start;
	GlobalTransition* _currGlobalTransition;
	Arabica::DOM::Document<std::string> _flatDoc;
	std::map<std::string, GlobalState*> _globalConf;
	std::map<std::string, GlobalState*> _activeConf; // potentially enabled transition sets per active configuration
	std::map<std::string, Arabica::DOM::Element<std::string> > _historyTargets; // ids of all history states
	
	friend class GlobalTransition;
	friend class GlobalState;
};

}

#endif /* end of include guard: CHARTTOFSM_H_IOKPYEBY */
