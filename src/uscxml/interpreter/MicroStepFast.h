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

#ifndef INTERPRETERFAST_H_DA55E52B
#define INTERPRETERFAST_H_DA55E52B

//#define USCXML_VERBOSE 1

#include <vector>
#include <set>
#include "MicroStepImpl.h"

#include <boost/dynamic_bitset.hpp>

namespace uscxml {

class MicroStepFast : public MicroStepImpl {
public:
	MicroStepFast(MicroStepCallbacks* callbacks);
	virtual ~MicroStepFast();

	virtual InterpreterState step(bool blocking);
	virtual void reset();
	virtual bool isInState(const std::string& stateId);
	virtual std::list<xercesc::DOMElement*> getConfiguration();
	void markAsCancelled();

protected:
	class Transition {
	public:
		Transition() : element(NULL), source(0), onTrans(NULL), type(0) {}

		xercesc::DOMElement* element;
		boost::dynamic_bitset<> conflicts;
		boost::dynamic_bitset<> exitSet;

		uint32_t source;
		boost::dynamic_bitset<> target;

		xercesc::DOMElement* onTrans;

		std::string event;
		std::string cond;

		unsigned char type;

	};

	class State {
	public:
		State() : element(NULL), parent(0), documentOrder(0), doneData(NULL), type(0) {}

		xercesc::DOMElement* element;
		boost::dynamic_bitset<> completion;
		boost::dynamic_bitset<> children;
		boost::dynamic_bitset<> ancestors;
		uint32_t parent;
		uint32_t documentOrder;

		std::list<xercesc::DOMElement*> data;
		std::list<xercesc::DOMElement*> invoke;
		std::list<xercesc::DOMElement*> onEntry;
		std::list<xercesc::DOMElement*> onExit;
		xercesc::DOMElement* doneData;

		unsigned char type;
	};

	virtual void init(xercesc::DOMElement* scxml);

	std::list<xercesc::DOMElement*> getCompletion(const xercesc::DOMElement* state);

	unsigned char _flags;
	std::map<std::string, int> _stateIds;

	std::vector<State*> _states;
	std::vector<Transition*> _transitions;
	std::list<xercesc::DOMElement*> _globalScripts;

	boost::dynamic_bitset<> _configuration;
	boost::dynamic_bitset<> _invocations;
	boost::dynamic_bitset<> _history;
	boost::dynamic_bitset<> _initializedData;

	std::set<boost::dynamic_bitset<> > _microstepConfigurations;

	Binding _binding;
	xercesc::DOMElement* _scxml;
	X _xmlPrefix;
	X _xmlNS;

	bool _isInitialized;
	bool _isCancelled;
	Event _event; // we do not care about the event's representation

private:
	std::list<xercesc::DOMElement*> getHistoryCompletion(const xercesc::DOMElement* state);
	void resortStates(xercesc::DOMNode* node, const X& xmlPrefix);

//    bool hasLegalConfiguration();

#ifdef USCXML_VERBOSE
	void printStateNames(const boost::dynamic_bitset<>& bitset);
#endif

};

}

#endif /* end of include guard: INTERPRETERFAST_H_DA55E52B */

