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
catch (Event e) { LOG(ERROR) << "Syntax error when calling " #callback " on monitors: " << std::endl << e << std::endl; } \
catch (std::bad_weak_ptr e) { LOG(ERROR) << "Unclean shutdown " << std::endl; } \
catch (...) { LOG(ERROR) << "An exception occurred when calling " #callback " on monitors"; } \
if (_state == USCXML_DESTROYED) { throw std::bad_weak_ptr(); }

#define USCXML_MONITOR_CALLBACK(callback, function) \
if (callback) { callback->function(); }

#define USCXML_MONITOR_CALLBACK1(callback, function, arg1) \
if (callback) { callback->function(arg1); }

#define USCXML_MONITOR_CALLBACK2(callback, function, arg1, arg2) \
if (callback) { callback->function(arg1, arg2); }

namespace uscxml {

class USCXML_API InterpreterMonitor {
public:
	InterpreterMonitor() : _copyToInvokers(false) {}
	virtual ~InterpreterMonitor() {}

	virtual void beforeProcessingEvent(const Event& event) {}
	virtual void beforeMicroStep() {}

	virtual void beforeExitingState(const XERCESC_NS::DOMElement* state) {}
	virtual void afterExitingState(const XERCESC_NS::DOMElement* state) {}

	virtual void beforeExecutingContent(const XERCESC_NS::DOMElement* execContent) {}
	virtual void afterExecutingContent(const XERCESC_NS::DOMElement* execContent) {}

	virtual void beforeUninvoking(const XERCESC_NS::DOMElement* invokeElem, const std::string& invokeid) {}
	virtual void afterUninvoking(const XERCESC_NS::DOMElement* invokeElem, const std::string& invokeid) {}

	virtual void beforeTakingTransition(const XERCESC_NS::DOMElement* transition) {}
	virtual void afterTakingTransition(const XERCESC_NS::DOMElement* transition) {}

	virtual void beforeEnteringState(const XERCESC_NS::DOMElement* state) {}
	virtual void afterEnteringState(const XERCESC_NS::DOMElement* state) {}

	virtual void beforeInvoking(const XERCESC_NS::DOMElement* invokeElem, const std::string& invokeid) {}
	virtual void afterInvoking(const XERCESC_NS::DOMElement* invokeElem, const std::string& invokeid) {}

	virtual void afterMicroStep() {}
	virtual void onStableConfiguration() {}

	virtual void beforeCompletion() {}
	virtual void afterCompletion() {}

	virtual void reportIssue(const InterpreterIssue& issue) {}

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

	virtual void beforeTakingTransition(const XERCESC_NS::DOMElement* transition);
	virtual void beforeExecutingContent(const XERCESC_NS::DOMElement* element);
	virtual void onStableConfiguration();
	virtual void beforeProcessingEvent(const uscxml::Event& event);
	virtual void beforeExitingState(const XERCESC_NS::DOMElement* state);
	virtual void beforeEnteringState(const XERCESC_NS::DOMElement* state);
	virtual void beforeMicroStep();

protected:
	static std::recursive_mutex _mutex;
};

}

#endif /* end of include guard: INTERPRETERMONITOR_H_D3F21429 */
