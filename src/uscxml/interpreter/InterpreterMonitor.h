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

#include "uscxml/config.h"
#include "uscxml/Common.h"
#include "uscxml/messages/Event.h"
#include "uscxml/debug/InterpreterIssue.h"

#include <mutex>

#define USCXML_MONITOR_CATCH(callback) \
catch (Event e) { LOG(ERROR) << "Syntax error when calling " #callback " on monitors: " << std::endl << e << std::endl; } \
catch (std::bad_weak_ptr e) { LOG(ERROR) << "Unclean shutdown " << std::endl; } \
catch (...) { LOG(ERROR) << "An exception occurred when calling " #callback " on monitors"; } \
if (_state == USCXML_DESTROYED) { throw std::bad_weak_ptr(); }

#define USCXML_MONITOR_CALLBACK(callbacks, function) \
for (auto callback : callbacks) { callback->function(_callbacks->getInterpreter()); }

#define USCXML_MONITOR_CALLBACK1(callbacks, function, arg1) \
for (auto callback : callbacks) { callback->function(_callbacks->getInterpreter(), arg1); }

#define USCXML_MONITOR_CALLBACK2(callbacks, function, arg1, arg2) \
for (auto callback : callbacks) { callback->function(_callbacks->getInterpreter(), arg1, arg2); }

// forward declare
namespace XERCESC_NS {
    class DOMElement;
}

namespace uscxml {

class USCXML_API InterpreterMonitor {
public:
	InterpreterMonitor() : _copyToInvokers(false) {}
	virtual ~InterpreterMonitor() {}

	virtual void beforeProcessingEvent(InterpreterImpl* impl, const Event& event) {}
	virtual void beforeMicroStep(InterpreterImpl* impl) {}

	virtual void beforeExitingState(InterpreterImpl* impl, const XERCESC_NS::DOMElement* state) {}
	virtual void afterExitingState(InterpreterImpl* impl, const XERCESC_NS::DOMElement* state) {}

	virtual void beforeExecutingContent(InterpreterImpl* impl, const XERCESC_NS::DOMElement* execContent) {}
	virtual void afterExecutingContent(InterpreterImpl* impl, const XERCESC_NS::DOMElement* execContent) {}

	virtual void beforeUninvoking(InterpreterImpl* impl, const XERCESC_NS::DOMElement* invokeElem, const std::string& invokeid) {}
	virtual void afterUninvoking(InterpreterImpl* impl, const XERCESC_NS::DOMElement* invokeElem, const std::string& invokeid) {}

	virtual void beforeTakingTransition(InterpreterImpl* impl, const XERCESC_NS::DOMElement* transition) {}
	virtual void afterTakingTransition(InterpreterImpl* impl, const XERCESC_NS::DOMElement* transition) {}

	virtual void beforeEnteringState(InterpreterImpl* impl, const XERCESC_NS::DOMElement* state) {}
	virtual void afterEnteringState(InterpreterImpl* impl, const XERCESC_NS::DOMElement* state) {}

	virtual void beforeInvoking(InterpreterImpl* impl, const XERCESC_NS::DOMElement* invokeElem, const std::string& invokeid) {}
	virtual void afterInvoking(InterpreterImpl* impl, const XERCESC_NS::DOMElement* invokeElem, const std::string& invokeid) {}

	virtual void afterMicroStep(InterpreterImpl* impl) {}
	virtual void onStableConfiguration(InterpreterImpl* impl) {}

	virtual void beforeCompletion(InterpreterImpl* impl) {}
	virtual void afterCompletion(InterpreterImpl* impl) {}

	virtual void reportIssue(InterpreterImpl* impl, const InterpreterIssue& issue) {}

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

	virtual void beforeTakingTransition(InterpreterImpl* impl, const XERCESC_NS::DOMElement* transition);
	virtual void beforeExecutingContent(InterpreterImpl* impl, const XERCESC_NS::DOMElement* element);
	virtual void onStableConfiguration(InterpreterImpl* impl);
	virtual void beforeProcessingEvent(InterpreterImpl* impl, const uscxml::Event& event);
	virtual void beforeExitingState(InterpreterImpl* impl, const XERCESC_NS::DOMElement* state);
	virtual void beforeEnteringState(InterpreterImpl* impl, const XERCESC_NS::DOMElement* state);
	virtual void beforeMicroStep(InterpreterImpl* impl);

protected:
	static std::recursive_mutex _mutex;
};

}

#endif /* end of include guard: INTERPRETERMONITOR_H_D3F21429 */
