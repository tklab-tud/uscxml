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
#include "uscxml/interpreter/Logging.h"
#include "uscxml/debug/InterpreterIssue.h"

#include <mutex>

#define USCXML_MONITOR_CATCH(callback) \
catch (Event e) { LOG(USCXML_ERROR) << "Syntax error when calling " #callback " on monitors: " << std::endl << e << std::endl; } \
catch (std::bad_weak_ptr e) { LOG(USCXML_ERROR) << "Unclean shutdown " << std::endl; } \
catch (...) { LOG(USCXML_ERROR) << "An exception occurred when calling " #callback " on monitors"; } \
if (_state == USCXML_DESTROYED) { throw std::bad_weak_ptr(); }

#define USCXML_MONITOR_CALLBACK(callbacks, function) { \
if (callbacks.size() > 0) {\
const std::string& inptr = _callbacks->getSessionId(); \
for (auto callback : callbacks) { callback->function(inptr); } } }

#define USCXML_MONITOR_CALLBACK1(callbacks, function, arg1) { \
if (callbacks.size() > 0) {\
const std::string& inptr = _callbacks->getSessionId(); \
for (auto callback : callbacks) { callback->function(inptr, arg1); } } }

#define USCXML_MONITOR_CALLBACK2(callbacks, function, arg1, arg2) { \
if (callbacks.size() > 0) {\
const std::string& inptr = _callbacks->getSessionId(); \
for (auto callback : callbacks) { callback->function(inptr, arg1, arg2); } } }

// forward declare
namespace XERCESC_NS {
class DOMElement;
}

namespace uscxml {

class Interpreter;

class USCXML_API InterpreterMonitor {
public:
	InterpreterMonitor() : _copyToInvokers(false) {
		_logger = Logger::getDefault();
	}
	InterpreterMonitor(Logger logger) : _copyToInvokers(false), _logger(logger) {}
	virtual ~InterpreterMonitor() {}

	virtual void beforeProcessingEvent(const std::string& sessionId, const Event& event) {}
	virtual void beforeMicroStep(const std::string& sessionId) {}

	virtual void beforeExitingState(const std::string& sessionId, const std::string& stateName, const XERCESC_NS::DOMElement* state) {}
	virtual void afterExitingState(const std::string& sessionId, const std::string& stateName, const XERCESC_NS::DOMElement* state) {}

	virtual void beforeExecutingContent(const std::string& sessionId, const XERCESC_NS::DOMElement* execContent) {}
	virtual void afterExecutingContent(const std::string& sessionId, const XERCESC_NS::DOMElement* execContent) {}

	virtual void beforeUninvoking(const std::string& sessionId, const XERCESC_NS::DOMElement* invokeElem, const std::string& invokeid) {}
	virtual void afterUninvoking(const std::string& sessionId, const XERCESC_NS::DOMElement* invokeElem, const std::string& invokeid) {}

	virtual void beforeTakingTransition(const std::string& sessionId, const XERCESC_NS::DOMElement* transition) {}
	virtual void afterTakingTransition(const std::string& sessionId, const XERCESC_NS::DOMElement* transition) {}

	virtual void beforeEnteringState(const std::string& sessionId, const std::string& stateName, const XERCESC_NS::DOMElement* state) {}
	virtual void afterEnteringState(const std::string& sessionId, const std::string& stateName, const XERCESC_NS::DOMElement* state) {}

	virtual void beforeInvoking(const std::string& sessionId, const XERCESC_NS::DOMElement* invokeElem, const std::string& invokeid) {}
	virtual void afterInvoking(const std::string& sessionId, const XERCESC_NS::DOMElement* invokeElem, const std::string& invokeid) {}

	virtual void afterMicroStep(const std::string& sessionId) {}
	virtual void onStableConfiguration(const std::string& sessionId) {}

	virtual void beforeCompletion(const std::string& sessionId) {}
	virtual void afterCompletion(const std::string& sessionId) {}

	virtual void reportIssue(const std::string& sessionId, const InterpreterIssue& issue) {}

	void copyToInvokers(bool copy) {
		_copyToInvokers = copy;
	}

	bool copyToInvokers() {
		return _copyToInvokers;
	}

protected:
	bool _copyToInvokers;
	Logger _logger;
};

class USCXML_API StateTransitionMonitor : public uscxml::InterpreterMonitor {
public:
	StateTransitionMonitor(std::string prefix = "") : _logPrefix(prefix) {}
	virtual ~StateTransitionMonitor() {}

	virtual void beforeTakingTransition(const std::string& sessionId, const XERCESC_NS::DOMElement* transition);
	virtual void beforeExecutingContent(const std::string& sessionId, const XERCESC_NS::DOMElement* element);
	virtual void onStableConfiguration(const std::string& sessionId);
	virtual void beforeProcessingEvent(const std::string& sessionId, const uscxml::Event& event);
	virtual void beforeExitingState(const std::string& sessionId, const std::string& stateName, const XERCESC_NS::DOMElement* state);
	virtual void beforeEnteringState(const std::string& sessionId, const std::string& stateName, const XERCESC_NS::DOMElement* state);
	virtual void beforeMicroStep(const std::string& sessionId);

protected:
	static std::recursive_mutex _mutex;
	std::string _logPrefix;
};

}

#endif /* end of include guard: INTERPRETERMONITOR_H_D3F21429 */
