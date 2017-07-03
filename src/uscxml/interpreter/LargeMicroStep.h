/**
 *  @file
 *  @author     2017 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

//#define USCXML_VERBOSE

#ifndef LARGEMICROSTEP_H_2573547
#define LARGEMICROSTEP_H_2573547

#include "uscxml/Common.h"
#include "uscxml/util/DOM.h" // X

#include "uscxml/util/Predicates.h"
#include "uscxml/util/String.h"
#include "uscxml/interpreter/InterpreterMonitor.h"

#include <boost/container/flat_set.hpp>
#include <boost/dynamic_bitset.hpp>

#include <vector>
#include <list>
#include <map>
#include "MicroStepImpl.h"

#ifdef _WIN32
#define BITSET_BLOCKTYPE size_t
#else
#define BITSET_BLOCKTYPE
#endif

namespace uscxml {

/**
 * @ingroup microstep
 * @ingroup impl
 *
 * MicroStep implementation with a more economic growth of data-structures for large state-charts.
 */
class LargeMicroStep : public MicroStepImpl {
public:

	LargeMicroStep(MicroStepCallbacks* callbacks);
	virtual ~LargeMicroStep();
	virtual std::shared_ptr<MicroStepImpl> create(MicroStepCallbacks* callbacks);

    std::string getName() { return "large"; }

	virtual InterpreterState step(size_t blockMs);
	virtual void reset();
	virtual bool isInState(const std::string& stateId);
	virtual std::list<XERCESC_NS::DOMElement*> getConfiguration();
	void markAsCancelled();

    virtual void deserialize(const Data& encodedState) {}
    virtual Data serialize() { return Data(); }

protected:
    LargeMicroStep() {} // only for the factory
    
	class State;
	class Transition;

    struct StateOrder
    {
        bool operator()(const State* lhs, const State* rhs) const  { return lhs->documentOrder < rhs->documentOrder; }
    };
    struct StateOrderPostFix
    {
        bool operator()(const State* lhs, const State* rhs) const  { return lhs->postFixOrder < rhs->postFixOrder; }
    };

    struct TransitionOrder
    {
        bool operator()(const Transition* lhs, const Transition* rhs) const  { return lhs->postFixOrder < rhs->postFixOrder; }
    };

    std::vector<State*> _states; ///< States in document order
    std::vector<Transition*> _transitions; ///< Transitions in reverse post-order

    boost::container::flat_set<State*, StateOrder> _configuration;
    boost::container::flat_set<State*, StateOrderPostFix> _configurationPostFix;
    boost::container::flat_set<State*, StateOrder> _invocations;
    boost::container::flat_set<State*, StateOrder> _history;
    boost::container::flat_set<State*, StateOrder> _initializedData;

	class Transition {
	public:
        Transition(uint32_t postFixOrder) : postFixOrder(postFixOrder) {}
        const uint32_t postFixOrder; // making these const increases performance somewhat

		XERCESC_NS::DOMElement* element = NULL;
        boost::container::flat_set<uint32_t> compatible;
        boost::container::flat_set<uint32_t> conflicting;
		std::pair<uint32_t, uint32_t> exitSet;

		State* source = NULL;
		std::vector<State*> target;

		XERCESC_NS::DOMElement* onTrans = NULL;

		std::string event;
		std::string cond;

		unsigned char type = 0;

	};

	class State {
	public:
        State(uint32_t documentOrder) : documentOrder(documentOrder) {}
        const uint32_t documentOrder;
        uint32_t postFixOrder;

		XERCESC_NS::DOMElement* element;
		boost::container::flat_set<State*, StateOrder> completion;
        boost::container::flat_set<State*, StateOrder> ancestors; // TODO: leverage!
		std::vector<State*> children;
		State* parent = NULL;

        std::vector<Transition*> transitions;
		std::vector<XERCESC_NS::DOMElement*> data;
		std::vector<XERCESC_NS::DOMElement*> invoke;
		std::vector<XERCESC_NS::DOMElement*> onEntry;
		std::vector<XERCESC_NS::DOMElement*> onExit;
		XERCESC_NS::DOMElement* doneData = NULL;

		unsigned char type;
	};

    void init(XERCESC_NS::DOMElement* scxml);

    std::list<XERCESC_NS::DOMElement*> getCompletion(const XERCESC_NS::DOMElement* state);
    std::list<XERCESC_NS::DOMElement*> getHistoryCompletion(const XERCESC_NS::DOMElement* history);

    unsigned char _flags = 0;
    boost::container::flat_set<boost::container::flat_set<State*, StateOrder> > _microstepConfigurations;

    bool _isInitialized = false;
    bool _isCancelled = false;
    Event _event; // we do not care about the event's representation

    std::list<XERCESC_NS::DOMElement*> _globalScripts;

    Binding _binding;
    XERCESC_NS::DOMElement* _scxml;
    X _xmlPrefix;
    X _xmlNS;
    
    /// Normalize order of elements per state
    void resortStates(XERCESC_NS::DOMElement* node, const X& xmlPrefix);

private:

    boost::container::flat_set<State*, StateOrder> _exitSet;
    boost::container::flat_set<State*, StateOrder> _entrySet;
    boost::container::flat_set<State*, StateOrder> _targetSet;
    boost::container::flat_set<State*, StateOrder> _tmpStates;
    
    boost::dynamic_bitset<BITSET_BLOCKTYPE> _compatible;
    boost::dynamic_bitset<BITSET_BLOCKTYPE> _conflicting;
    
    boost::container::flat_set<Transition*, TransitionOrder> _transSet;

    // adapted from http://www.cplusplus.com/reference/algorithm/set_intersection/
    template <class iter_t1, class iter_t2, class compare = StateOrder>
    bool intersects(iter_t1 first1, iter_t1 last1, iter_t2 first2, iter_t2 last2) {
        while (first1 != last1 && first2 != last2) {
            if (compare()(*first1, *first2)) {
                ++first1;
            } else if (compare()(*first2, *first1)) {
                ++first2;
            } else {
                return true;
            }
        }
        return false;
    }

    bool isInFinal(const State* state);
    void printStateNames(const boost::container::flat_set<LargeMicroStep::State*, LargeMicroStep::StateOrder>& a);

    uint32_t getTransitionDomain(const Transition* transition);
    std::pair<uint32_t, uint32_t> getExitSet(const Transition* transition);
    std::map<uint32_t, std::pair<uint32_t, uint32_t> > _exitSetCache;

    friend class Factory;
};

}
#endif /* end of include guard: LARGEMICROSTEP_H_2573547 */
