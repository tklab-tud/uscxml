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

#include "uscxml/debug/DebugSession.h"
#include "uscxml/debug/Debugger.h"
#include "uscxml/util/Predicates.h"

#include "uscxml/interpreter/Logging.h"

namespace uscxml {

void DebugSession::checkBreakpoints(const std::list<Breakpoint> qualifiedBreakpoints) {
	std::list<Breakpoint>::const_iterator qualifiedBreakpointIter = qualifiedBreakpoints.begin();

	if (!_breakpointsEnabled)
		return;

	while(qualifiedBreakpointIter != qualifiedBreakpoints.end()) {
		const Breakpoint& qualifiedBreakpoint = *qualifiedBreakpointIter++;

		// check if one of the user-supplied breakpoints match
		bool userBreakpointMatched = false;
		Data replyData;

		if (_skipTo) {
			if (_skipTo.matches(_interpreter, qualifiedBreakpoint)) {
				replyData.compound["breakpoint"] = _skipTo.toData();
				replyData.compound["qualified"] = qualifiedBreakpoint.toData();
				breakExecution(replyData);
				_skipTo = Breakpoint();
			}
			continue;
		}

		std::set<Breakpoint>::const_iterator breakpointIter = _breakPoints.begin();
		while(breakpointIter != _breakPoints.end()) {
			const Breakpoint& breakpoint = *breakpointIter++;
			if (!breakpoint.enabled)
				continue;
			if (breakpoint.matches(_interpreter, qualifiedBreakpoint)) {
				// do we have a condition?

				replyData.compound["breakpoint"] = breakpoint.toData();
				replyData.compound["qualified"] = qualifiedBreakpoint.toData();

				userBreakpointMatched = true;
				breakExecution(replyData);
			}
		}
		if (_isStepping && !userBreakpointMatched) {
			replyData.compound["qualified"] = qualifiedBreakpoint.toData();
			breakExecution(replyData);

		}
	}
}

void DebugSession::breakExecution(Data replyData) {
	std::lock_guard<std::recursive_mutex> lock(_mutex);

	std::list<XERCESC_NS::DOMElement*> configuration = _interpreter.getConfiguration();
	int index = 0;
	for (auto state : configuration) {
		if (HAS_ATTR(state, kXMLCharId)) {
			replyData.compound["activeStates"].array.insert(std::make_pair(index++,Data(ATTR(state, kXMLCharId), Data::VERBATIM)));
			if (isAtomic(state)) {
				replyData.compound["basicStates"].array.insert(std::make_pair(index++,Data(ATTR(state, kXMLCharId), Data::VERBATIM)));
			}
		}
	}

	replyData.compound["replyType"] = Data("breakpoint", Data::VERBATIM);
	_debugger->pushData(shared_from_this(), replyData);

	// wait for resume from the client
	_resumeCond.wait(_mutex);
}

Data DebugSession::debugPrepare(const Data& data) {
	Data replyData;

	if (!data.hasKey("xml") && !data.hasKey("url")) {
		replyData.compound["status"] = Data("failure", Data::VERBATIM);
		replyData.compound["reason"] = Data("No XML or URL given", Data::VERBATIM);
		return replyData;
	}

	debugStop(data);

	_isAttached = false;

	try {
		if (data.hasKey("xml")) {
			_interpreter = Interpreter::fromXML(data.at("xml").atom, (data.hasKey("url") ? data.at("url").atom : ""));
		} else if (data.hasKey("url")) {
			_interpreter = Interpreter::fromURL(data.at("url").atom);
		} else {
			_interpreter = Interpreter();
		}
	} catch(ErrorEvent e) {
		log(USCXML_ERROR, e);
	} catch(...) {}

	if (_interpreter) {
		// register ourself as a monitor
		_interpreter.addMonitor(_debugger);
		_debugger->attachSession(_interpreter.getImpl().get(), shared_from_this());

		replyData.compound["status"] = Data("success", Data::VERBATIM);
	} else {
		replyData.compound["status"] = Data("failure", Data::VERBATIM);
	}

	return replyData;
}

Data DebugSession::debugAttach(const Data& data) {
	Data replyData;
	_isAttached = true;

	if (!data.hasKey("attach")) {
		replyData.compound["status"] = Data("failure", Data::VERBATIM);
		replyData.compound["reason"] = Data("No id to attach to given", Data::VERBATIM);
		return replyData;
	}

	std::string interpreterId = data.at("attach").atom;
	bool interpreterFound = false;

	// find interpreter for sessionid
	std::map<std::string, std::weak_ptr<InterpreterImpl> > instances = InterpreterImpl::getInstances();
	for (auto weakInstance : instances) {

		std::shared_ptr<InterpreterImpl> instance = weakInstance.second.lock();
		if (instance && instance->getSessionId() == interpreterId) {
			_interpreter = instance;
			_debugger->attachSession(_interpreter.getImpl().get(), shared_from_this());
			interpreterFound = true;
			break;
		}
	}

	if (!interpreterFound) {
		replyData.compound["status"] = Data("failure", Data::VERBATIM);
		replyData.compound["reason"] = Data("No interpreter with given id found", Data::VERBATIM);
	} else {
		replyData.compound["xml"].node = _interpreter.getImpl()->getDocument();
		replyData.compound["status"] = Data("success", Data::VERBATIM);
	}

	return replyData;
}

Data DebugSession::debugDetach(const Data& data) {
	Data replyData;
	_isAttached = false;

	_debugger->detachSession(_interpreter.getImpl().get());
	replyData.compound["status"] = Data("success", Data::VERBATIM);
	return replyData;
}

Data DebugSession::debugStart(const Data& data) {
	Data replyData;

	if (_isAttached) {
		replyData.compound["reason"] = Data("Already started when attached", Data::VERBATIM);
		replyData.compound["status"] = Data("failure", Data::VERBATIM);
	} else if (!_interpreter) {
		replyData.compound["reason"] = Data("No interpreter attached or loaded", Data::VERBATIM);
		replyData.compound["status"] = Data("failure", Data::VERBATIM);
	} else {
		_isRunning = true;
		_interpreterThread = new std::thread(DebugSession::run, this);
		replyData.compound["status"] = Data("success", Data::VERBATIM);
	}

	return replyData;
}

void DebugSession::run(void* instance) {
	DebugSession* INSTANCE = (DebugSession*)instance;

#ifdef APPLE
	std::string threadName;
	threadName += "uscxml::";
	threadName += (INSTANCE->_interpreter.getImpl()->_name.size() > 0 ? INSTANCE->_interpreter.getImpl()->_name : "anon");
	threadName += ".debug";

	pthread_setname_np(threadName.c_str());
#endif

	InterpreterState state = USCXML_UNDEF;
	while(state != USCXML_FINISHED && INSTANCE->_isRunning) {
		state = INSTANCE->_interpreter.step();

		//		if (!INSTANCE->_isStarted) {
		//			// we have been cancelled
		//			INSTANCE->_isActive = false;
		//			return;
		//		}
	}
	LOG(INSTANCE->_interpreter.getLogger(), USCXML_DEBUG) << "done" << std::endl;
}

Data DebugSession::debugStop(const Data& data) {
	Data replyData;

	if (_interpreter) {
		// detach from old intepreter
		_debugger->detachSession(_interpreter.getImpl().get());
	}

	if (_isRunning && _interpreterThread != NULL) {
		_isRunning = false;

		// unblock
		_resumeCond.notify_all();

		_interpreterThread->join();
		delete(_interpreterThread);
	}

	_skipTo = Breakpoint();
	replyData.compound["status"] = Data("success", Data::VERBATIM);

	// calls destructor
	_interpreter = Interpreter();

	return replyData;
}

Data DebugSession::debugStep(const Data& data) {
	std::lock_guard<std::recursive_mutex> lock(_mutex);

	stepping(true);
	_resumeCond.notify_one();

	Data replyData;
	if (_interpreter) {
		// register ourself as a monitor
		if (!_isRunning) {
			_isRunning = true;
			_interpreterThread = new std::thread(DebugSession::run, this);

		}

		replyData.compound["status"] = Data("success", Data::VERBATIM);
	} else {
		replyData.compound["status"] = Data("failure", Data::VERBATIM);
	}
	return replyData;
}

Data DebugSession::debugResume(const Data& data) {
	std::lock_guard<std::recursive_mutex> lock(_mutex);

	stepping(false);

	Data replyData;
	replyData.compound["status"] = Data("success", Data::VERBATIM);

	_resumeCond.notify_one();
	return replyData;
}


Data DebugSession::debugPause(const Data& data) {
	std::lock_guard<std::recursive_mutex> lock(_mutex);

	_skipTo = Breakpoint();
	stepping(true);

	Data replyData;
	replyData.compound["status"] = Data("success", Data::VERBATIM);

	return replyData;
}

Data DebugSession::skipToBreakPoint(const Data& data) {
	std::lock_guard<std::recursive_mutex> lock(_mutex);

	_skipTo = Breakpoint(data);
	Data replyData;

	if (_interpreter) {
		// register ourself as a monitor
		if (!_isRunning) {
			_isRunning = true;
			_interpreterThread = new std::thread(DebugSession::run, this);
		}

		replyData.compound["status"] = Data("success", Data::VERBATIM);
	} else {
		replyData.compound["status"] = Data("failure", Data::VERBATIM);
	}

	_resumeCond.notify_one();
	return replyData;
}

Data DebugSession::addBreakPoint(const Data& data) {
	Breakpoint breakpoint(data);

	Data replyData;
	if (_breakPoints.find(breakpoint) == _breakPoints.end()) {
		_breakPoints.insert(breakpoint);
		replyData.compound["status"] = Data("success", Data::VERBATIM);

	} else {
		replyData.compound["reason"] = Data("Breakpoint already exists", Data::VERBATIM);
		replyData.compound["status"] = Data("failure", Data::VERBATIM);
	}
	return replyData;
}

Data DebugSession::removeBreakPoint(const Data& data) {
	Breakpoint breakpoint(data);

	Data replyData;
	if (_breakPoints.find(breakpoint) != _breakPoints.end()) {
		_breakPoints.erase(breakpoint);
		replyData.compound["status"] = Data("success", Data::VERBATIM);
	} else {
		replyData.compound["reason"] = Data("No such breakpoint", Data::VERBATIM);
		replyData.compound["status"] = Data("failure", Data::VERBATIM);
	}
	return replyData;
}

Data DebugSession::enableBreakPoint(const Data& data) {
	Breakpoint breakpoint(data);

	Data replyData;
	if (_breakPoints.find(breakpoint) != _breakPoints.end()) {
		_breakPoints.find(breakpoint)->enabled = true;
		replyData.compound["status"] = Data("success", Data::VERBATIM);
	} else {
		replyData.compound["reason"] = Data("No such breakpoint", Data::VERBATIM);
		replyData.compound["status"] = Data("failure", Data::VERBATIM);
	}

	return replyData;
}
Data DebugSession::disableBreakPoint(const Data& data) {
	Breakpoint breakpoint(data);

	Data replyData;
	if (_breakPoints.find(breakpoint) != _breakPoints.end()) {
		_breakPoints.find(breakpoint)->enabled = false;
		replyData.compound["status"] = Data("success", Data::VERBATIM);
	} else {
		replyData.compound["reason"] = Data("No such breakpoint", Data::VERBATIM);
		replyData.compound["status"] = Data("failure", Data::VERBATIM);
	}

	return replyData;
}
Data DebugSession::enableAllBreakPoints() {
	Data replyData;

	_breakpointsEnabled = true;
	replyData.compound["status"] = Data("success", Data::VERBATIM);

	return replyData;
}

Data DebugSession::disableAllBreakPoints() {
	Data replyData;

	_breakpointsEnabled = false;
	replyData.compound["status"] = Data("success", Data::VERBATIM);

	return replyData;
}

Data DebugSession::getIssues() {
	Data replyData;

	std::list<InterpreterIssue> issues = _interpreter.validate();
	replyData.compound["status"] = Data("success", Data::VERBATIM);
	int index = 0;
	for (auto issue : issues) {
		Data issueData;

		issueData.compound["message"] = Data(issue.message, Data::VERBATIM);
		issueData.compound["xPath"] = Data(issue.xPath, Data::VERBATIM);
		issueData.compound["specRef"] = Data(issue.specRef, Data::VERBATIM);

		switch (issue.severity) {
		case InterpreterIssue::USCXML_ISSUE_FATAL:
			issueData.compound["severity"] = Data("FATAL", Data::VERBATIM);
			break;
		case InterpreterIssue::USCXML_ISSUE_WARNING:
			issueData.compound["severity"] = Data("WARN", Data::VERBATIM);
			break;
		case InterpreterIssue::USCXML_ISSUE_INFO:
			issueData.compound["severity"] = Data("INFO", Data::VERBATIM);
			break;
		default:
			break;
		}
		replyData.compound["issues"].array.insert(std::make_pair(index++,issueData));
	}

	return replyData;
}

Data DebugSession::debugEval(const Data& data) {
	Data replyData;

	if (!data.hasKey("expression")) {
		replyData.compound["status"] = Data("failure", Data::VERBATIM);
		replyData.compound["reason"] = Data("No expression given", Data::VERBATIM);
		return replyData;
	}

	std::string expr = data.at("expression").atom;

	if (!_interpreter) {
		replyData.compound["status"] = Data("failure", Data::VERBATIM);
		replyData.compound["reason"] = Data("No interpreter running", Data::VERBATIM);
	} else if (!_interpreter.getImpl()->_dataModel) {
		replyData.compound["status"] = Data("failure", Data::VERBATIM);
		replyData.compound["reason"] = Data("No datamodel available", Data::VERBATIM);
	} else {
		try {
			replyData.compound["eval"] = _interpreter.getImpl()->getAsData(expr);
		} catch (Event e) {
			replyData.compound["eval"] = e.data;
			replyData.compound["eval"].compound["error"] = Data(e.name, Data::VERBATIM);
		}
		replyData.compound["status"] = Data("success", Data::VERBATIM);
	}
	return replyData;
}

std::shared_ptr<LoggerImpl> DebugSession::create() {
	return shared_from_this();
}

void DebugSession::log(LogSeverity severity, const Event& event) {
	Data d;
	d.compound["data"] = event.data;
	d.compound["name"] = Data(event.name);
	d.compound["origin"] = Data(event.origin);
	d.compound["origintype"] = Data(event.origintype);

	switch (event.eventType) {
	case Event::Type::INTERNAL:
		d.compound["eventType"] = Data("INTERNAL");
		break;
	case Event::Type::EXTERNAL:
		d.compound["eventType"] = Data("EXTERNAL");
		break;
	case Event::Type::PLATFORM:
		d.compound["eventType"] = Data("PLATFORM");
		break;
	default:
		break;
	}
	if (!event.hideSendId)
		d.compound["sendid"] = Data(event.sendid);
	if (event.invokeid.size() > 0)
		d.compound["invokeid"] = Data(event.invokeid);

	// handle params
	Data& params = d.compound["params"];
	bool convertedToArray = false;
	int index = 0;
	for (auto param : event.params) {
		if (params.compound.find(param.first) != d.compound.end()) {
			// no such key, add as literal data
			d.compound[param.first] = param.second;
		} else if (params.compound[param.first].array.size() > 0 && convertedToArray) {
			// key is already an array
			params.compound[param.first].array.insert(std::make_pair(index++,param.second));
		} else {
			// key already given as literal data, move to array
			Data& existingParam = params.compound[param.first];
			params.compound[param.first].array.insert(std::make_pair(index++,existingParam));
			params.compound[param.first].array.insert(std::make_pair(index++, param.second));
			params.compound[param.first].compound.clear();
			convertedToArray = true;
		}
	}

	// handle namelist
	Data& namelist = d.compound["namelist"];
	for (auto name : event.namelist) {
		namelist.compound[name.first] = name.second;
	}

	_debugger->pushData(shared_from_this(), d);
}

void DebugSession::log(LogSeverity severity, const Data& data) {
	_debugger->pushData(shared_from_this(), data);
}

void DebugSession::log(LogSeverity severity, const std::string& message) {
	_debugger->pushData(shared_from_this(), Data(message));
}

}
