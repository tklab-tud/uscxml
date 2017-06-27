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

#include "uscxml/config.h"
#include "uscxml/Common.h"
#include "uscxml/util/DOM.h" // X

#include "uscxml/util/Predicates.h"
#include "uscxml/util/String.h"
#include "uscxml/interpreter/InterpreterMonitor.h"

/* flat_set is 10 times faster than std::set here */
#include <boost/container/flat_set.hpp>

#include <vector>
#include <list>
#include <map>
#include "MicroStepImpl.h"

namespace uscxml {

/**
 * @ingroup microstep
 * @ingroup impl
 */
class LargeMicroStep : public MicroStepImpl {
public:

	LargeMicroStep(MicroStepCallbacks* callbacks);
	virtual ~LargeMicroStep();
	virtual std::shared_ptr<MicroStepImpl> create(MicroStepCallbacks* callbacks);

	virtual InterpreterState step(size_t blockMs);
	virtual void reset();
	virtual bool isInState(const std::string& stateId);
	virtual std::list<XERCESC_NS::DOMElement*> getConfiguration();
	void markAsCancelled();

    virtual void deserialize(const Data& encodedState) {}
    virtual Data serialize() { return Data(); }

protected:
	class State;
	class Transition;

    struct StateOrder
    {
        bool operator()(const State* lhs, const State* rhs) const  { return lhs->documentOrder < rhs->documentOrder; }
    };

    struct TransitionOrder
    {
        bool operator()(const Transition* lhs, const Transition* rhs) const  { return lhs->postFixOrder < rhs->postFixOrder; }
    };

    std::vector<State*> _states; ///< States in document order
    std::vector<Transition*> _transitions; ///< Transitions in reverse post-order

    boost::container::flat_set<State*, StateOrder> _configuration;
    boost::container::flat_set<State*, StateOrder> _invocations;
    boost::container::flat_set<State*, StateOrder> _history;
    boost::container::flat_set<State*, StateOrder> _initializedData;

	class Transition {
	public:
        Transition(uint32_t postFixOrder) : postFixOrder(postFixOrder) {}
        const uint32_t postFixOrder; // making these const increases performance somewhat

		XERCESC_NS::DOMElement* element = NULL;
		boost::container::flat_set<Transition*, TransitionOrder> compatible;
		boost::container::flat_set<State*, StateOrder> exitSet;

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

		XERCESC_NS::DOMElement* element;
		boost::container::flat_set<State*, StateOrder> completion;
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
    
    boost::container::flat_set<Transition*, TransitionOrder> _compatible;
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

};

}
#endif /* end of include guard: LARGEMICROSTEP_H_2573547 */
