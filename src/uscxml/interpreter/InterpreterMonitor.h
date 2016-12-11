/**
 *  @file
 *  @author     2016 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#ifndef INTERPRETERMONITOR_H_D3F21429
#define INTERPRETERMONITOR_H_D3F21429

#include "uscxml/Common.h"
#include "uscxml/messages/Event.h"
#include "uscxml/debug/InterpreterIssue.h"

#include <mutex>

#define USCXML_MONITOR_CATCH(callback) \
catch (Event e) { LOG(USCXML_ERROR) << "Syntax error when calling " #callback " on monitors: " << std::endl << e << std::endl; } \
catch (std::bad_weak_ptr e) { LOG(USCXML_ERROR) << "Unclean shutdown " << std::endl; } \
catch (...) { LOG(USCXML_ERROR) << "An exception occurred when calling " #callback " on monitors"; } \
if (_state == USCXML_DESTROYED) { throw std::bad_weak_ptr(); }

#define USCXML_MONITOR_CALLBACK(callbacks, function) { \
Interpreter inptr = _callbacks->getInterpreter(); \
for (auto callback : callbacks) { callback->function(inptr); } }

#define USCXML_MONITOR_CALLBACK1(callbacks, function, arg1) { \
Interpreter inptr = _callbacks->getInterpreter(); \
for (auto callback : callbacks) { callback->function(inptr, arg1); } }

#define USCXML_MONITOR_CALLBACK2(callbacks, function, arg1, arg2) { \
Interpreter inptr = _callbacks->getInterpreter(); \
for (auto callback : callbacks) { callback->function(inptr, arg1, arg2); } }

// forward declare
namespace XERCESC_NS {
class DOMElement;
}

namespace uscxml {

class Interpreter;

class USCXML_API InterpreterMonitor {
public:
	InterpreterMonitor() : _copyToInvokers(false) {}
	virtual ~InterpreterMonitor() {}

	virtual void beforeProcessingEvent(Interpreter& interpreter, const Event& event) {}
	virtual void beforeMicroStep(Interpreter& interpreter) {}

	virtual void beforeExitingState(Interpreter& interpreter, const XERCESC_NS::DOMElement* state) {}
	virtual void afterExitingState(Interpreter& interpreter, const XERCESC_NS::DOMElement* state) {}

	virtual void beforeExecutingContent(Interpreter& interpreter, const XERCESC_NS::DOMElement* execContent) {}
	virtual void afterExecutingContent(Interpreter& interpreter, const XERCESC_NS::DOMElement* execContent) {}

	virtual void beforeUninvoking(Interpreter& interpreter, const XERCESC_NS::DOMElement* invokeElem, const std::string& invokeid) {}
	virtual void afterUninvoking(Interpreter& interpreter, const XERCESC_NS::DOMElement* invokeElem, const std::string& invokeid) {}

	virtual void beforeTakingTransition(Interpreter& interpreter, const XERCESC_NS::DOMElement* transition) {}
	virtual void afterTakingTransition(Interpreter& interpreter, const XERCESC_NS::DOMElement* transition) {}

	virtual void beforeEnteringState(Interpreter& interpreter, const XERCESC_NS::DOMElement* state) {}
	virtual void afterEnteringState(Interpreter& interpreter, const XERCESC_NS::DOMElement* state) {}

	virtual void beforeInvoking(Interpreter& interpreter, const XERCESC_NS::DOMElement* invokeElem, const std::string& invokeid) {}
	virtual void afterInvoking(Interpreter& interpreter, const XERCESC_NS::DOMElement* invokeElem, const std::string& invokeid) {}

	virtual void afterMicroStep(Interpreter& interpreter) {}
	virtual void onStableConfiguration(Interpreter& interpreter) {}

	virtual void beforeCompletion(Interpreter& interpreter) {}
	virtual void afterCompletion(Interpreter& interpreter) {}

	virtual void reportIssue(Interpreter& interpreter, const InterpreterIssue& issue) {}

	void copyToInvokers(bool copy) {
		_copyToInvokers = copy;
	}

	bool copyToInvokers() {
		return _copyToInvokers;
	}

protected:
	bool _copyToInvokers;

};

class USCXML_API StateTransitionMonitor : public uscxml::InterpreterMonitor {
public:
	StateTransitionMonitor() {}
	virtual ~StateTransitionMonitor() {}

	virtual void beforeTakingTransition(Interpreter& interpreter, const XERCESC_NS::DOMElement* transition);
	virtual void beforeExecutingContent(Interpreter& interpreter, const XERCESC_NS::DOMElement* element);
	virtual void onStableConfiguration(Interpreter& interpreter);
	virtual void beforeProcessingEvent(Interpreter& interpreter, const uscxml::Event& event);
	virtual void beforeExitingState(Interpreter& interpreter, const XERCESC_NS::DOMElement* state);
	virtual void beforeEnteringState(Interpreter& interpreter, const XERCESC_NS::DOMElement* state);
	virtual void beforeMicroStep(Interpreter& interpreter);

protected:
	static std::recursive_mutex _mutex;
};

}

#endif /* end of include guard: INTERPRETERMONITOR_H_D3F21429 */
