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

#ifndef DEBUGSESSION_H_M8YHEGV6
#define DEBUGSESSION_H_M8YHEGV6

#include "uscxml/debug/Breakpoint.h"
#include "uscxml/Interpreter.h"
#include "uscxml/interpreter/LoggingImpl.h"

#include <time.h>
#include <set>
#include <thread>
#include <condition_variable>
#include <mutex>

namespace uscxml {

class Debugger;

class USCXML_API DebugSession : public LoggerImpl ,public std::enable_shared_from_this<DebugSession> {
public:
	DebugSession() {
		_isRunning = false;
		_isStepping = false;
		_isAttached = false;
		_breakpointsEnabled = true;
		_markedForDeletion = false;
		_debugger = NULL;
	}

	void stepping(bool enable) {
		_isStepping = enable;
	}

	void checkBreakpoints(const std::list<Breakpoint> qualifiedBreakpoints);

	Data debugPrepare(const Data& data);
	Data debugAttach(const Data& data);
	Data debugDetach(const Data& data);
	Data debugStart(const Data& data);
	Data debugStop(const Data& data);
	Data debugStep(const Data& data);
	Data debugResume(const Data& data);
	Data debugPause(const Data& data);
	Data skipToBreakPoint(const Data& data);
	Data addBreakPoint(const Data& data);
	Data removeBreakPoint(const Data& data);
	Data enableBreakPoint(const Data& data);
	Data disableBreakPoint(const Data& data);
	Data enableAllBreakPoints();
	Data disableAllBreakPoints();
	Data debugEval(const Data& data);

	void setDebugger(Debugger* debugger) {
		_debugger = debugger;
	}

	Interpreter getInterpreter() {
		return _interpreter;
	}

	void markForDeletion(bool mark) {
		_markedForDeletion = mark;
	}

    // Logger
    virtual std::shared_ptr<LoggerImpl> create();
    
    virtual void log(LogSeverity severity, const Event& event);
    virtual void log(LogSeverity severity, const Data& data);
    virtual void log(LogSeverity severity, const std::string& message);

protected:
	void breakExecution(Data replyData);

	bool _isStepping;
	bool _isAttached;
	bool _breakpointsEnabled;

	std::condition_variable_any _resumeCond;
	std::recursive_mutex _runMutex;
	std::recursive_mutex _mutex;

	std::thread* _interpreterThread = NULL;
	bool _isRunning;
	static void run(void* instance);

	bool _markedForDeletion;
	Debugger* _debugger;
	Interpreter _interpreter;
	std::set<Breakpoint> _breakPoints;
	Breakpoint _skipTo;

	friend class Debugger;
};


}


#endif /* end of include guard: DEBUGSESSION_H_M8YHEGV6 */
