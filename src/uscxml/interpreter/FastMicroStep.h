/**
 *  @file
 *  @author     2012-2016 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#ifndef FASTMICROSTEP_H_065FE1F7
#define FASTMICROSTEP_H_065FE1F7

//#define USCXML_VERBOSE 1

#include "uscxml/config.h"
#include "uscxml/Common.h"
#include "uscxml/util/DOM.h" // X

#include <vector>
#include <map>
#include <set>
#include "MicroStepImpl.h"

#include <boost/dynamic_bitset.hpp>

namespace uscxml {

/**
 * @ingroup microstep
 * @ingroup impl
 */
class FastMicroStep : public MicroStepImpl {
public:
	FastMicroStep(MicroStepCallbacks* callbacks);
	virtual ~FastMicroStep();
	virtual std::shared_ptr<MicroStepImpl> create(MicroStepCallbacks* callbacks);

	virtual InterpreterState step(size_t blockMs);
	virtual void reset();
	virtual bool isInState(const std::string& stateId);
	virtual std::list<XERCESC_NS::DOMElement*> getConfiguration();
	void markAsCancelled();

protected:
	class Transition {
	public:
		Transition() : element(NULL), source(0), onTrans(NULL), type(0) {}

		XERCESC_NS::DOMElement* element;
		boost::dynamic_bitset<> conflicts;
		boost::dynamic_bitset<> exitSet;

		uint32_t source;
		boost::dynamic_bitset<> target;

		XERCESC_NS::DOMElement* onTrans;

		std::string event;
		std::string cond;

		unsigned char type;

	};

	class State {
	public:
		State() : element(NULL), parent(0), documentOrder(0), doneData(NULL), type(0) {}

		XERCESC_NS::DOMElement* element;
		boost::dynamic_bitset<> completion;
		boost::dynamic_bitset<> children;
		boost::dynamic_bitset<> ancestors;
		uint32_t parent;
		uint32_t documentOrder;

		std::list<XERCESC_NS::DOMElement*> data;
		std::list<XERCESC_NS::DOMElement*> invoke;
		std::list<XERCESC_NS::DOMElement*> onEntry;
		std::list<XERCESC_NS::DOMElement*> onExit;
		XERCESC_NS::DOMElement* doneData;

		unsigned char type;
	};

	class CachedPredicates {
	public:
		std::map<const XERCESC_NS::DOMElement*, std::list<XERCESC_NS::DOMElement*> > exitSet;
	};

	virtual void init(XERCESC_NS::DOMElement* scxml);

	std::list<XERCESC_NS::DOMElement*> getCompletion(const XERCESC_NS::DOMElement* state);

	unsigned char _flags;
	std::map<std::string, int> _stateIds;

	std::vector<State*> _states;
	std::vector<Transition*> _transitions;
	std::list<XERCESC_NS::DOMElement*> _globalScripts;

	boost::dynamic_bitset<> _configuration;
	boost::dynamic_bitset<> _invocations;
	boost::dynamic_bitset<> _history;
	boost::dynamic_bitset<> _initializedData;

	std::set<boost::dynamic_bitset<> > _microstepConfigurations;

	Binding _binding;
	XERCESC_NS::DOMElement* _scxml;
	X _xmlPrefix;
	X _xmlNS;

	bool _isInitialized;
	bool _isCancelled;
	Event _event; // we do not care about the event's representation

private:
	std::list<XERCESC_NS::DOMElement*> getHistoryCompletion(const XERCESC_NS::DOMElement* state);
	void resortStates(XERCESC_NS::DOMElement* node, const X& xmlPrefix);

	bool conflictsCached(const XERCESC_NS::DOMElement* t1, const XERCESC_NS::DOMElement* t2, const XERCESC_NS::DOMElement* root); ///< overrides implementation Predicates::conflicts for speed

	std::list<XERCESC_NS::DOMElement*> getExitSetCached(const XERCESC_NS::DOMElement* transition,
	        const XERCESC_NS::DOMElement* root);

	CachedPredicates _cache;

#ifdef USCXML_VERBOSE
	void printStateNames(const boost::dynamic_bitset<>& bitset);
#endif

};

}

#endif /* end of include guard: FASTMICROSTEP_H_065FE1F7 */

