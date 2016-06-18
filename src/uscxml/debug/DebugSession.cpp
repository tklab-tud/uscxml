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
    for (auto state : configuration) {
        if (HAS_ATTR(state, "id")) {
            replyData.compound["activeStates"].array.push_back(Data(ATTR(state, "id"), Data::VERBATIM));
            if (isAtomic(state)) {
                replyData.compound["basicStates"].array.push_back(Data(ATTR(state, "id"), Data::VERBATIM));
            }
        }
    }

	replyData.compound["replyType"] = Data("breakpoint", Data::VERBATIM);
	_debugger->pushData(shared_from_this(), replyData);
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

	if (data.hasKey("xml")) {
        _interpreter = Interpreter::fromXML(data.at("xml").atom, (data.hasKey("url") ? data.at("url").atom : ""));
	} else if (data.hasKey("url")) {
		_interpreter = Interpreter::fromURL(data.at("url").atom);
	} else {
		_interpreter = Interpreter();
	}

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
		//_interpreter.start();
        assert(false);

		replyData.compound["status"] = Data("success", Data::VERBATIM);
	}

	return replyData;
}

Data DebugSession::debugStop(const Data& data) {
	Data replyData;

	if (_interpreter) {
		// detach from old intepreter
		_debugger->detachSession(_interpreter.getImpl().get());
	}

	if (_interpreter && !_isAttached)
        assert(false);
        //_interpreter.stop();
	// unblock
	_resumeCond.notify_all();

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
		if (!_isRunning)
			//_interpreter.start();
            assert(false);

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
	replyData.compound["status"] = Data("success", Data::VERBATIM);

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


}