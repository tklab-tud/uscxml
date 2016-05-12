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

#ifndef INTERPRETERMONITOR_H_4BA77097
#define INTERPRETERMONITOR_H_4BA77097

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

	virtual void beforeExitingState(const xercesc::DOMElement* state) {}
	virtual void afterExitingState(const xercesc::DOMElement* state) {}

	virtual void beforeExecutingContent(const xercesc::DOMElement* execContent) {}
	virtual void afterExecutingContent(const xercesc::DOMElement* execContent) {}

	virtual void beforeUninvoking(const xercesc::DOMElement* invokeElem, const std::string& invokeid) {}
	virtual void afterUninvoking(const xercesc::DOMElement* invokeElem, const std::string& invokeid) {}

	virtual void beforeTakingTransition(const xercesc::DOMElement* transition) {}
	virtual void afterTakingTransition(const xercesc::DOMElement* transition) {}

	virtual void beforeEnteringState(const xercesc::DOMElement* state) {}
	virtual void afterEnteringState(const xercesc::DOMElement* state) {}

	virtual void beforeInvoking(const xercesc::DOMElement* invokeElem, const std::string& invokeid) {}
	virtual void afterInvoking(const xercesc::DOMElement* invokeElem, const std::string& invokeid) {}

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

}

#endif /* end of include guard: INTERPRETERMONITOR_H_4BA77097 */
