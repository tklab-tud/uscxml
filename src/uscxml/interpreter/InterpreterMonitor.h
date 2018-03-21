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

#include <functional>
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

	virtual void beforeProcessingEvent(const std::string& sessionId,
	                                   const Event& event) {}
	virtual void beforeMicroStep(const std::string& sessionId) {}

	virtual void beforeExitingState(const std::string& sessionId,
	                                const std::string& stateName,
	                                const XERCESC_NS::DOMElement* state) {}
	virtual void afterExitingState(const std::string& sessionId,
	                               const std::string& stateName,
	                               const XERCESC_NS::DOMElement* state) {}

	virtual void beforeExecutingContent(const std::string& sessionId,
	                                    const XERCESC_NS::DOMElement* execContent) {}
	virtual void afterExecutingContent(const std::string& sessionId,
	                                   const XERCESC_NS::DOMElement* execContent) {}

	virtual void beforeUninvoking(const std::string& sessionId,
	                              const XERCESC_NS::DOMElement* invokeElem,
	                              const std::string& invokeid) {}
	virtual void afterUninvoking(const std::string& sessionId,
	                             const XERCESC_NS::DOMElement* invokeElem,
	                             const std::string& invokeid) {}

	virtual void beforeTakingTransition(const std::string& sessionId,
	                                    const XERCESC_NS::DOMElement* transition) {}
	virtual void afterTakingTransition(const std::string& sessionId,
	                                   const XERCESC_NS::DOMElement* transition) {}

	virtual void beforeEnteringState(const std::string& sessionId,
	                                 const std::string& stateName,
	                                 const XERCESC_NS::DOMElement* state) {}
	virtual void afterEnteringState(const std::string& sessionId,
	                                const std::string& stateName,
	                                const XERCESC_NS::DOMElement* state) {}

	virtual void beforeInvoking(const std::string& sessionId,
	                            const XERCESC_NS::DOMElement* invokeElem,
	                            const std::string& invokeid) {}
	virtual void afterInvoking(const std::string& sessionId,
	                           const XERCESC_NS::DOMElement* invokeElem,
	                           const std::string& invokeid) {}

	virtual void afterMicroStep(const std::string& sessionId) {}
	virtual void onStableConfiguration(const std::string& sessionId) {}

	virtual void beforeCompletion(const std::string& sessionId) {}
	virtual void afterCompletion(const std::string& sessionId) {}

	virtual void reportIssue(const std::string& sessionId,
	                         const InterpreterIssue& issue) {}

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

class USCXML_API LambdaMonitor : public InterpreterMonitor {
public:
	void processEvent(std::function<void (const std::string& sessionId,
	                                      const Event& event)> callback) {
		_beforeProcessingEvent = callback;
	}


	void microStep(std::function<void (const std::string& sessionId)> callback,
	               bool after = false) {
		if (after) {
			_afterMicroStep = callback;
		} else {
			_beforeMicroStep = callback;
		}

	}

	void exitState(std::function<void (const std::string& sessionId,
	                                   const std::string& stateName,
	                                   const XERCESC_NS::DOMElement* state)> callback,
	               bool after = false) {
		if (after) {
			_afterExitingState = callback;
		} else {
			_beforeExitingState = callback;
		}
	}

	void executeContent(std::function<void (const std::string& sessionId,
	                                        const XERCESC_NS::DOMElement* execContent)> callback,
	                    bool after = false) {
		if (after) {
			_afterExecutingContent = callback;
		} else {
			_beforeExecutingContent = callback;
		}
	}

	void uninvoke(std::function<void (const std::string& sessionId,
	                                  const XERCESC_NS::DOMElement* invokeElem,
	                                  const std::string& invokeid)> callback,
	              bool after = false) {
		if (after) {
			_afterUninvoking = callback;
		} else {
			_beforeUninvoking = callback;
		}
	}

	void transition(std::function<void (const std::string& sessionId,
	                                    const XERCESC_NS::DOMElement* transition)> callback,
	                bool after = false) {
		if (after) {
			_afterTakingTransition = callback;
		} else {
			_beforeTakingTransition = callback;
		}
	}

	void enterState(std::function<void (const std::string& sessionId,
	                                    const std::string& stateName,
	                                    const XERCESC_NS::DOMElement* state)> callback,
	                bool after = false) {
		_beforeEnteringState = callback;
		if (after) {
			_afterEnteringState = callback;
		} else {
			_beforeEnteringState = callback;
		}

	}

	void invoke(std::function<void (const std::string& sessionId,
	                                const XERCESC_NS::DOMElement* invokeElem,
	                                const std::string& invokeid)> callback,
	            bool after = false) {
		if (after) {
			_afterInvoking = callback;
		} else {
			_beforeInvoking = callback;
		}
	}

	void stableConfiguration(std::function<void (const std::string& sessionId)> callback) {
		_onStableConfiguration = callback;
	}

	void completion(std::function<void (const std::string& sessionId)> callback,
	                bool after = false) {
		if (after) {
			_afterCompletion = callback;
		} else {
			_beforeCompletion = callback;
		}

	}

	void reportIssue(std::function<void (const std::string& sessionId,
	                                     const InterpreterIssue& issue)> callback) {
		_reportIssue = callback;
	}

protected:

	std::function<void (const std::string& sessionId,
	                    const Event& event)> _beforeProcessingEvent;

	std::function<void (const std::string& sessionId)> _beforeMicroStep;

	std::function<void (const std::string& sessionId,
	                    const std::string& stateName,
	                    const XERCESC_NS::DOMElement* state)> _beforeExitingState;

	std::function<void (const std::string& sessionId,
	                    const std::string& stateName,
	                    const XERCESC_NS::DOMElement* state)> _afterExitingState;

	std::function<void (const std::string& sessionId,
	                    const XERCESC_NS::DOMElement* execContent)> _beforeExecutingContent;
	std::function<void (const std::string& sessionId,
	                    const XERCESC_NS::DOMElement* execContent)> _afterExecutingContent;

	std::function<void (const std::string& sessionId,
	                    const XERCESC_NS::DOMElement* invokeElem,
	                    const std::string& invokeid)> _beforeUninvoking;
	std::function<void (const std::string& sessionId,
	                    const XERCESC_NS::DOMElement* invokeElem,
	                    const std::string& invokeid)> _afterUninvoking;

	std::function<void (const std::string& sessionId,
	                    const XERCESC_NS::DOMElement* transition)> _beforeTakingTransition;
	std::function<void (const std::string& sessionId,
	                    const XERCESC_NS::DOMElement* transition)> _afterTakingTransition;

	std::function<void (const std::string& sessionId,
	                    const std::string& stateName,
	                    const XERCESC_NS::DOMElement* state)> _beforeEnteringState;
	std::function<void (const std::string& sessionId,
	                    const std::string& stateName,
	                    const XERCESC_NS::DOMElement* state)> _afterEnteringState;

	std::function<void (const std::string& sessionId,
	                    const XERCESC_NS::DOMElement* invokeElem,
	                    const std::string& invokeid)> _beforeInvoking;
	std::function<void (const std::string& sessionId,
	                    const XERCESC_NS::DOMElement* invokeElem,
	                    const std::string& invokeid)> _afterInvoking;

	std::function<void (const std::string& sessionId)> _afterMicroStep;
	std::function<void (const std::string& sessionId)> _onStableConfiguration;

	std::function<void (const std::string& sessionId)> _beforeCompletion;
	std::function<void (const std::string& sessionId)> _afterCompletion;

	std::function<void (const std::string& sessionId,
	                    const InterpreterIssue& issue)> _reportIssue;



	void beforeProcessingEvent(const std::string& sessionId,
	                           const Event& event) {
		if (_beforeProcessingEvent)
			_beforeProcessingEvent(sessionId, event);
	}
	void beforeMicroStep(const std::string& sessionId) {
		if (_beforeMicroStep)
			_beforeMicroStep(sessionId);
	}

	void beforeExitingState(const std::string& sessionId,
	                        const std::string& stateName,
	                        const XERCESC_NS::DOMElement* state) {
		if (_beforeExitingState)
			_beforeExitingState(sessionId, stateName, state);
	}

	void afterExitingState(const std::string& sessionId,
	                       const std::string& stateName,
	                       const XERCESC_NS::DOMElement* state) {
		if (_afterExitingState)
			_afterExitingState(sessionId, stateName, state);
	}

	void beforeExecutingContent(const std::string& sessionId,
	                            const XERCESC_NS::DOMElement* execContent) {
		if (_beforeExecutingContent)
			_beforeExecutingContent(sessionId, execContent);
	}
	void afterExecutingContent(const std::string& sessionId,
	                           const XERCESC_NS::DOMElement* execContent) {
		if (_afterExecutingContent)
			_afterExecutingContent(sessionId, execContent);

	}

	void beforeUninvoking(const std::string& sessionId,
	                      const XERCESC_NS::DOMElement* invokeElem,
	                      const std::string& invokeid) {
		if (_beforeUninvoking)
			_beforeUninvoking(sessionId, invokeElem, invokeid);
	}
	void afterUninvoking(const std::string& sessionId,
	                     const XERCESC_NS::DOMElement* invokeElem,
	                     const std::string& invokeid) {
		if (_afterUninvoking)
			_afterUninvoking(sessionId, invokeElem, invokeid);
	}

	void beforeTakingTransition(const std::string& sessionId,
	                            const XERCESC_NS::DOMElement* transition) {
		if (_beforeTakingTransition)
			_beforeTakingTransition(sessionId, transition);
	}
	void afterTakingTransition(const std::string& sessionId,
	                           const XERCESC_NS::DOMElement* transition) {
		if (_afterTakingTransition)
			_afterTakingTransition(sessionId, transition);
	}

	void beforeEnteringState(const std::string& sessionId,
	                         const std::string& stateName,
	                         const XERCESC_NS::DOMElement* state) {
		if (_beforeEnteringState)
			_beforeEnteringState(sessionId, stateName, state);
	}
	void afterEnteringState(const std::string& sessionId,
	                        const std::string& stateName,
	                        const XERCESC_NS::DOMElement* state) {
		if (_afterEnteringState)
			_afterEnteringState(sessionId, stateName, state);
	}

	void beforeInvoking(const std::string& sessionId,
	                    const XERCESC_NS::DOMElement* invokeElem,
	                    const std::string& invokeid) {
		if (_beforeInvoking)
			_beforeInvoking(sessionId, invokeElem, invokeid);
	}
	void afterInvoking(const std::string& sessionId,
	                   const XERCESC_NS::DOMElement* invokeElem,
	                   const std::string& invokeid) {
		if (_afterInvoking)
			_afterInvoking(sessionId, invokeElem, invokeid);
	}

	void afterMicroStep(const std::string& sessionId) {
		if (_afterMicroStep)
			_afterMicroStep(sessionId);
	}
	void onStableConfiguration(const std::string& sessionId) {
		if (_onStableConfiguration)
			_onStableConfiguration(sessionId);
	}

	void beforeCompletion(const std::string& sessionId) {
		if (_beforeCompletion)
			_beforeCompletion(sessionId);
	}
	void afterCompletion(const std::string& sessionId) {
		if (_afterCompletion)
			_afterCompletion(sessionId);
	}

	void reportIssue(const std::string& sessionId,
	                 const InterpreterIssue& issue) {
		if (_reportIssue)
			_reportIssue(sessionId, issue);
	}
};

}

#endif /* end of include guard: INTERPRETERMONITOR_H_D3F21429 */
