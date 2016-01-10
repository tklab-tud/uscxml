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

#ifndef CHARTTOMINIMALSCXML_H_7B97677A
#define CHARTTOMINIMALSCXML_H_7B97677A

#include "uscxml/DOMUtils.h"
#include "uscxml/interpreter/InterpreterRC.h"
#include <DOM/Document.hpp>
#include <DOM/Node.hpp>
#include <XPath/XPath.hpp>
#include <ostream>
#include <list>
#include <set>

#include "Transformer.h"

namespace uscxml {

class USCXML_API ChartToMinimalSCXML : public InterpreterRC, public StateTransitionMonitor, public TransformerImpl {
public:
	virtual ~ChartToMinimalSCXML() {}
	static Transformer transform(const Interpreter& other);

	// InterpreterMonitor
	virtual void beforeExecutingContent(Interpreter interpreter, const Arabica::DOM::Element<std::string>& element);
	virtual void beforeUninvoking(Interpreter interpreter, const Arabica::DOM::Element<std::string>& invokeElem, const std::string& invokeid);
	virtual void beforeTakingTransition(Interpreter interpreter, const Arabica::DOM::Element<std::string>& transition, bool moreComing);
	virtual void beforeEnteringState(Interpreter interpreter, const Arabica::DOM::Element<std::string>& state, bool moreComing);
	virtual void beforeInvoking(Interpreter interpreter, const Arabica::DOM::Element<std::string>& invokeElem, const std::string& invokeid);
	virtual void beforeCompletion(Interpreter interpreter);
	virtual void onStableConfiguration(Interpreter interpreter);

	// gather executable content per microstep
	void executeContent(const Arabica::DOM::Element<std::string>& content, bool rethrow = false);

	// invoke and uninvoke
	virtual void invoke(const Arabica::DOM::Element<std::string>& element);
	virtual void cancelInvoke(const Arabica::DOM::Element<std::string>& element);

protected:
	void writeTo(std::ostream& stream);

	ChartToMinimalSCXML(const Interpreter& other);

	void markAsVisited(const Arabica::DOM::Element<std::string>& element);
	void removeUnvisited(Arabica::DOM::Node<std::string>& node);

	std::set<Arabica::DOM::Node<std::string> > _visited;
	DataModel _dmCopy;
	bool _retainAsComments;

private:
	size_t _step;

	// we need this to register as an instance at Interpreter::_instances
	boost::shared_ptr<InterpreterImpl> _selfPtr;

	// prevent deletion from shared_ptr
	class Deleter {
	public:
		void operator()(ChartToMinimalSCXML* p) {
			/* do nothing */
		}
	};

};

}


#endif /* end of include guard: CHARTTOMINIMALSCXML_H_7B97677A */
