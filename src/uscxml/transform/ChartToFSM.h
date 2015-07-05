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


class USCXML_API GlobalState {
public:

	GlobalState() {}
	GlobalState(const Arabica::DOM::Node<std::string>& globalState);
	GlobalState(const Arabica::XPath::NodeSet<std::string>& activeStates,
	            const Arabica::XPath::NodeSet<std::string>& alreadyEnteredStates, // we need to remember for binding=late
	            const std::map<std::string, Arabica::XPath::NodeSet<std::string> >& historyStates,
	            const std::string& xmlNSPrefix,
							ChartToFSM* flattener);

	std::set<int> activeStatesRefs;
	std::set<int> alreadyEnteredStatesRefs;
	std::map<std::string, std::set<int> > historyStatesRefs;
	
	std::list<GlobalTransition*> sortedOutgoing;
	std::string stateId;
	std::string activeId;

	unsigned long activeIndex;
	unsigned long index;
	bool isFinal;
	
	ChartToFSM* interpreter;
	
	Arabica::XPath::NodeSet<std::string> getActiveStates();
	Arabica::XPath::NodeSet<std::string> getAlreadyEnteredStates();
	std::map<std::string, Arabica::XPath::NodeSet<std::string> > getHistoryStates();

//	friend class ChartToFSM;
};


class USCXML_API GlobalTransition {
public:
	enum InvalidReason {
		MIXES_EVENT_SPONTANEOUS,
		NO_COMMON_EVENT,
		CHILD_ENABLED,
		SAME_SOURCE_STATE,
		UNCONDITIONAL_SUPERSET,
		UNCONDITIONAL_MATCH,
		PREEMPTING_MEMBERS
	};

	class Action {
	public:
		bool operator<(const Action& other) const {
			if ((onEntry && !other.onEntry) || (!onEntry && other.onEntry))
				return true;
			if ((raiseDone && !other.raiseDone) || (!raiseDone && other.raiseDone))
				return true;
			if ((onExit && !other.onExit) || (!onExit && other.onExit))
				return true;
			if ((transition && !other.transition) || (!transition && other.transition))
				return true;
			if ((entered && !other.entered) || (!entered && other.entered))
				return true;
			if ((exited && !other.exited) || (!exited && other.exited))
				return true;
			if ((invoke && !other.invoke) || (!invoke && other.invoke))
				return true;
			if ((uninvoke && !other.uninvoke) || (!uninvoke && other.uninvoke))
				return true;
			
			if (onEntry < other.onEntry)
				return onEntry < other.onEntry;
			if (raiseDone < other.raiseDone)
				return raiseDone < other.raiseDone;
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
		
		friend USCXML_API std::ostream& operator<< (std::ostream& os, const Action& action);

		typedef std::list<GlobalTransition::Action>::iterator iter_t;
		
		Arabica::DOM::Element<std::string> onEntry;
		Arabica::DOM::Element<std::string> onExit;
		Arabica::DOM::Element<std::string> transition;
		Arabica::DOM::Element<std::string> entered;
		Arabica::DOM::Element<std::string> exited;
		Arabica::DOM::Element<std::string> invoke;
		Arabica::DOM::Element<std::string> uninvoke;
		Arabica::DOM::Element<std::string> raiseDone;
		
	};

	GlobalTransition(const Arabica::XPath::NodeSet<std::string>& transitions, DataModel dataModel, ChartToFSM* flattener);
	static GlobalTransition* copyWithoutExecContent(GlobalTransition* other);
	
	bool isValid; // constructor will determine, calling code will delete if not
	std::string invalidMsg;
	InvalidReason invalidReason;

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

USCXML_API std::ostream& operator<< (std::ostream& os, const GlobalTransition::Action& action);

class TransitionTreeNode {
public:
	enum TransitionTreeNodeType {
		TYPE_UNDEFINED,
		TYPE_PARALLEL,
		TYPE_NESTED,
		TYPE_TRANSITION
	};
	
	TransitionTreeNode()
	: prevTransition(NULL),
		nextTransition(NULL),
		firstTransition(NULL),
		firstState(NULL),
		parent(NULL),
		type(TYPE_UNDEFINED) {}
	
	virtual ~TransitionTreeNode() {
		for (std::list<TransitionTreeNode*>::iterator childIter = children.begin(); childIter != children.end(); childIter++) {
			delete(*childIter);
		}
	}

	void dump(int indent = 0);

	TransitionTreeNode* prevTransition;
	TransitionTreeNode* nextTransition;
	Arabica::DOM::Element<std::string> transition;

	Arabica::DOM::Element<std::string> state;
	TransitionTreeNode* firstTransition;
	TransitionTreeNode* lastTransition;
	TransitionTreeNode* firstState;

	TransitionTreeNode* parent;
	std::list<TransitionTreeNode*> children;
	std::string nodeId;

	TransitionTreeNodeType type;
	
	bool operator<(const TransitionTreeNode& other) const {
		return nodeId < other.nodeId;
	}

};

class USCXML_API ChartToFSM : public InterpreterRC, public InterpreterMonitor {
public:
	ChartToFSM(const Interpreter& other);
	virtual ~ChartToFSM();

	void indexTransitions();
	Arabica::DOM::Document<std::string> getDocument() const; // overwrite to return flat FSM

protected:

	InterpreterState interpret();
		
	GlobalState* _start;
	Arabica::DOM::Document<std::string> _flatDoc;
	std::map<std::string, GlobalState*> _globalConf;
	std::map<std::string, GlobalState*> _activeConf; // potentially enabled transition sets per active configuration
	std::map<std::string, Arabica::DOM::Element<std::string> > _historyTargets; // ids of all history states

	uint32_t getMinInternalQueueLength(uint32_t defaultVal);
	uint32_t getMinExternalQueueLength(uint32_t defaultVal);

	bool _keepInvalidTransitions;
	bool _transitionsFromTree;

	std::vector<Arabica::DOM::Element<std::string> > indexedTransitions;
	std::vector<Arabica::DOM::Element<std::string> > indexedStates;

private:
	Arabica::XPath::NodeSet<std::string> refsToStates(const std::set<int>&);
	Arabica::XPath::NodeSet<std::string> refsToTransitions(const std::set<int>&);
	
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
	void getPotentialTransitionsForConfFromPowerSet(const Arabica::XPath::NodeSet<std::string>& conf, std::map<std::string, GlobalTransition*>& outMap);
	void getPotentialTransitionsForConfFromTree(const Arabica::XPath::NodeSet<std::string>& conf, std::map<std::string, GlobalTransition*>& outMap);
//	void labelTransitions();
	TransitionTreeNode* buildTransTree(const Arabica::DOM::Element<std::string>& root, const std::string& nodeId);

	void indexTransitions(const Arabica::DOM::Element<std::string>& root);
	void annotateRaiseAndSend(const Arabica::DOM::Element<std::string>& root);
	bool hasForeachInBetween(const Arabica::DOM::Node<std::string>& ancestor, const Arabica::DOM::Node<std::string>& child);
	void updateRaisedAndSendChains(GlobalState* state, GlobalTransition* source, std::set<GlobalTransition*> visited);

	void reassembleFromFlat();
	
	std::list<GlobalTransition*> sortTransitions(std::list<GlobalTransition*> list);

	// we need this static as we use it in a sort function
	static std::map<Arabica::DOM::Node<std::string>, Arabica::DOM::Node<std::string> > _transParents;
	
	static bool filterSameState(const Arabica::XPath::NodeSet<std::string>& transitions);

	uint64_t _perfTransProcessed;
	uint64_t _perfTransTotal;
	uint64_t _perfTransUsed;
	uint64_t _perfStatesProcessed;
	uint64_t _perfStatesTotal;
	uint64_t _perfStatesSkippedProcessed;
	uint64_t _perfStatesSkippedTotal;
	uint64_t _perfStatesCachedProcessed;
	uint64_t _perfStatesCachedTotal;
	uint64_t _perfMicroStepProcessed;
	uint64_t _perfMicroStepTotal;
	uint64_t _perfStackSize;
	uint64_t _lastTimeStamp;

	size_t _lastTransientStateId;
	size_t _lastStateIndex;
	size_t _lastActiveIndex;
	size_t _lastTransIndex;

	bool _alreadyFlat;

	bool _skipEventChainCalculations;
	size_t _maxEventSentChain;
	size_t _maxEventRaisedChain;
	size_t _doneEventRaiseTolerance;
	
	GlobalTransition* _currGlobalTransition;
	std::map<std::string, std::map<std::string, GlobalTransition*> > _confToTransitions;
	
	TransitionTreeNode* _transTree;
	std::map<Arabica::DOM::Element<std::string>, TransitionTreeNode*> _stateToTransTreeNode;
	
	friend class GlobalTransition;
	friend class GlobalState;
};

}

#endif /* end of include guard: CHARTTOFSM_H_IOKPYEBY */
