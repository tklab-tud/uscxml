/**
 *  @file
 *  @author     2012-2013 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#ifndef POSTPONEELEMENT_H_WN8EIYYI
#define POSTPONEELEMENT_H_WN8EIYYI

#include <uscxml/Interpreter.h>
#include <list>

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class PostponeElement : public ExecutableContentImpl {
public:
	struct Postponed {
		Postponed(const Event& event, const std::string& until, long timeout, bool chaining = false) :
			event(event), until(until), timeout(timeout), chaining(chaining) {}
		Event event;
		std::string until;
		uint64_t timeout;
		bool chaining;
	};

	PostponeElement() {}
	virtual ~PostponeElement() {}
	boost::shared_ptr<ExecutableContentImpl> create(InterpreterImpl* interpreter);

	std::string getLocalName() {
		return "postpone";
	}

	std::string getNamespace() {
		return "http://www.w3.org/2005/07/scxml";
	}

	bool processChildren() {
		return false;
	}

	void enterElement(const Arabica::DOM::Element<std::string>& node);
	void exitElement(const Arabica::DOM::Element<std::string>& node);

protected:
	// once per interpreter
	class Resubmitter : public InterpreterMonitor {
	public:
		Resubmitter(InterpreterImpl* interpreter) {
			interpreter->addMonitor(this);
		}

		static Resubmitter* getInstance(InterpreterImpl* interpreter);
		static void postpone(const Event& event, std::string until, uint64_t timeout, bool chained, InterpreterImpl* interpreter);

		// InterpreterMonitor
		void onStableConfiguration(Interpreter interpreter);
		void afterCompletion(Interpreter interpreter);

		std::list<Postponed> _postponedEvents;
		static std::map<Interpreter, Resubmitter*> _instances;
		static tthread::recursive_mutex _accessLock;

	};
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(PostponeElement, ExecutableContentImpl);
#endif

}

#endif /* end of include guard: POSTPONEELEMENT_H_WN8EIYYI */
