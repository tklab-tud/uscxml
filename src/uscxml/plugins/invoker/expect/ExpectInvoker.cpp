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

#include "ExpectInvoker.h"
#include <glog/logging.h>

#include "uscxml/concurrency/eventqueue/DelayedEventQueue.h"

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

#include "uscxml/UUID.h"

#undef USE_TCL_STUBS

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool pluginConnect(pluma::Host& host) {
	host.add( new ExpectInvokerProvider() );
	return true;
}
#endif

Tcl_Interp* ExpectInvoker::_tcl = NULL;

ExpectInvoker::ExpectInvoker() : _eventQueue(NULL) {
}

ExpectInvoker::~ExpectInvoker() {
	_eventQueue->stop();
//	if (_tcl) {
//		Tcl_DeleteInterp(_tcl);
//	}
};

boost::shared_ptr<InvokerImpl> ExpectInvoker::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<ExpectInvoker> invoker = boost::shared_ptr<ExpectInvoker>(new ExpectInvoker());
	return invoker;
}

Data ExpectInvoker::getDataModelVariables() {
	Data data;
	return data;
}

void ExpectInvoker::send(const SendRequest& req) {
	EventContext* ctx = new EventContext();
	ctx->sendReq = req;
	ctx->instance = this;

//	LOG(ERROR) << "################ " << req;

	std::string eventId = UUID::getUUID();
	_eventQueue->addEvent(eventId, ExpectInvoker::send, 0, ctx);

//	send(ctx, "");
}

void ExpectInvoker::send(void *userdata, const std::string event) {

	EventContext* ctx = (EventContext*)userdata;
	if (!ctx)
		return;

	if (!ctx->instance) {
		delete(ctx);
		return;
	}

	const SendRequest& req = ctx->sendReq;

	if (iequals(req.name, "expect.match")) {
		int nrCases = req.params.size();
		struct exp_case *cases = (struct exp_case*)malloc(sizeof(struct exp_case) * (nrCases + 1));
		memset(cases, 0, sizeof(exp_case) * (nrCases + 1));

		/**
		 exp_end: indicates that no more  patterns appear.
		 exp_glob: indicates that the pattern is a glob-style string pattern.
		 exp_exact: indicates that the pattern is an exact string.
		 exp_regexp: indicates that the pattern is a regexp-style string pattern.
		 exp_compiled: indicates that the pattern is a regexp-style string pattern, and that its compiled form is also provided.
		 exp_null: indicates that the pattern is a null (for debugging purposes, a string pattern must also follow).
		*/

		Event::params_t::const_iterator paramIter = req.params.begin();
		int index = 0;
		while (paramIter != req.params.end()) {
			struct exp_case* expCase = &cases[index];
			size_t colonPos = paramIter->first.find(":");
			if (colonPos != std::string::npos) {
				if (paramIter->first.substr(0, colonPos) == "regex") {
					expCase->type = exp_regexp;
				} else if(paramIter->first.substr(0, colonPos) == "glob") {
					expCase->type = exp_glob;
				} else if(paramIter->first.substr(0, colonPos) == "exact") {
					expCase->type = exp_exact;
				} else {
					// if we can't make sense of the type
					expCase->type = exp_exact;
				}
			} else {
				expCase->type = exp_regexp;
			}

			expCase->pattern = strdup(paramIter->second.atom.c_str());
//			LOG(ERROR) << "################ " << expCase->pattern;

			if (expCase->type == exp_regexp) {
				expCase->re = TclRegComp(expCase->pattern);
				if (expCase->re == NULL) {
					LOG(ERROR) << TclGetRegError();
					expCase->type = exp_null;
				}
			}
			expCase->value = index + 1;
			paramIter++;
			index++;
		}

		assert(index == nrCases);

		cases[nrCases].type = exp_end;

		/**
		 * The functions wait until the output from a process matches one of the
		 * patterns, a specified time period has passed, or an EOF is seen.
		 */

		int rc = 0;
		// exp_fexpectv won't return on timeout when called in thread
//		rc = exp_fexpectv(ctx->instance->_cmdFP, cases);
		rc = exp_expectv(ctx->instance->_cmdFD, cases);

		if (rc == EXP_EOF) {
			Event ev;
			ev.name = "expect.match.eof";
			ev.data.compound["buffer"] = Data(exp_buffer, Data::VERBATIM);
			ctx->instance->returnEvent(ev);
		} else if (rc == EXP_TIMEOUT) {
			Event ev;
			ev.name = "expect.match.timeout";
			ev.data.compound["buffer"] = Data(exp_buffer, Data::VERBATIM);
			ctx->instance->returnEvent(ev);
		} else if (rc == EXP_FULLBUFFER) {
			Event ev;
			ev.name = "expect.match.fullbuffer";
			ev.data.compound["buffer"] = Data(exp_buffer, Data::VERBATIM);
			ctx->instance->returnEvent(ev);
		} else if (rc > 0) {
			rc--; // we started at 1
			paramIter = req.params.begin();
			while(rc > 0) {
				if (paramIter == req.params.end())
					break;
				paramIter++;
				rc--;
			}
			if (paramIter != req.params.end()) {
				Event event;

				size_t colonPos = paramIter->first.find(":");
				if (colonPos != std::string::npos) {
					std::string eventName = paramIter->first;
					event.name = std::string("expect.match.") + eventName.substr(colonPos + 1, eventName.length() - (colonPos + 1));
					event.data.compound["type"] = Data(paramIter->first.substr(0, colonPos), Data::VERBATIM);

				} else {
					event.name = std::string("expect.match.") + paramIter->first;
					event.data.compound["type"] = Data("regex", Data::VERBATIM);
				}

				event.data.compound["pattern"] = Data(paramIter->second.atom, Data::VERBATIM);
				event.data.compound["buffer"] = Data(exp_buffer, Data::VERBATIM);
				event.data.compound["start"] = Data((int)(exp_match - exp_buffer));
				event.data.compound["end"] = Data((int)(exp_match_end - exp_buffer));
				event.data.compound["match"] = Data(std::string(exp_buffer).substr(exp_match - exp_buffer, exp_match_end - exp_match), Data::VERBATIM);
				ctx->instance->returnEvent(event);
			} else {
				// exp_fexpectl returned gibberish
				assert(false);
			}
		} else {
			// exp_fexpectl returned gibberish
			assert(false);
		}

		// free our memory
		for (int i = 0; i < nrCases; i++) {
			if (cases[i].pattern != NULL)
				free(cases[i].pattern);
			if (cases[i].re != NULL)
				free(cases[i].re);
		}
		free(cases);

	} else if (iequals(req.name, "expect.send")) {
		std::string toSend = unescape(req.content);
		ctx->instance->_interpreter->getDataModel().replaceExpressions(toSend);
		fwrite(toSend.c_str(), toSend.length(), 1, ctx->instance->_cmdFP);
	}

	delete(ctx);
}

void ExpectInvoker::cancel(const std::string sendId) {
}

void ExpectInvoker::invoke(const InvokeRequest& req) {
	if (_eventQueue == NULL) {
		_eventQueue = new DelayedEventQueue();
		_eventQueue->start();
	}

	EventContext* ctx = new EventContext();
	ctx->invokeReq = req;
	ctx->instance = this;

	//_eventQueue->addEvent(req.sendid, ExpectInvoker::invoke, 0, ctx);
	invoke(ctx, "");

}

void ExpectInvoker::invoke(void *userdata, const std::string event) {
	EventContext* ctx = (EventContext*)userdata;

	if (!ctx)
		return;

	if (!ctx->instance) {
		delete(ctx);
		return;
	}

	const InvokeRequest& req = ctx->invokeReq;

	// moved here for thread local storage
	if (ctx->instance->_tcl == NULL) {
		ctx->instance->_tcl = Tcl_CreateInterp();
		if (ctx->instance->_tcl) {
			Tcl_Init(ctx->instance->_tcl);
			Expect_Init(ctx->instance->_tcl);
		}
		ctx->instance->_cmdFP = NULL;

		bool debug = false;
		Event::getParam(req.params, "debug", debug);
		if (debug) {
			exp_is_debugging = 1;
		} else {
			exp_is_debugging = 0;
		}

		int timeout = 20;
		Event::getParam(req.params, "timeout", timeout);
		exp_timeout = timeout;

		bool logUser = false;
		Event::getParam(req.params, "loguser", logUser);
		if (logUser) {
			exp_loguser = 1;
		} else {
			exp_loguser = 0;
		}

		// exp_interactive = 1;
		exp_logfile = 0;
		// exp_remove_nulls = 1;
		// exp_ttyinit = 1;

	} else {
//		assert(false);
	}

	char* cmd = NULL;
	char** args = NULL;
	int nrArgs = 0;

	if (req.params.count("spawn")) {
		// get command
		std::string command;
		Event::getParam(req.params, "spawn", command);
		cmd = strdup(command.c_str());

		// get arguments
		nrArgs = req.params.count("argument");
		args = (char**)malloc(sizeof(char*) * nrArgs + 2);
		args[0] = strdup(command.c_str());

		size_t index = 1;
		std::pair<Event::params_t::const_iterator, Event::params_t::const_iterator> argIterRange = req.params.equal_range("argument");
		Event::params_t::const_iterator argIter = argIterRange.first;
		while(argIter != argIterRange.second) {
			args[index] = strdup(argIter->second.atom.c_str());
			argIter++;
			index++;
		}
		args[index] = (char*)0;
	} else if(req.params.count("command")) {

	}

	// open socket
	ctx->instance->_cmdFD = exp_spawnv(cmd, args);
	if (ctx->instance->_cmdFD > 0) {
		ctx->instance->_cmdFP = fdopen(ctx->instance->_cmdFD, "r+");

		if (ctx->instance->_cmdFP) {
			// disable buffering
			setbuf(ctx->instance->_cmdFP,(char *)0);
			Event event;
			event.name = "spawn.success";
			ctx->instance->returnEvent(event);
		}
	}

	if (ctx->instance->_cmdFP == NULL || ctx->instance->_cmdFD <= 0) {
		Event event;
		event.name = "spawn.failed";
		event.data.compound["cause"] = Data(strerror(errno), Data::VERBATIM);
		Tcl_Obj *infoObj = Tcl_GetVar2Ex(_tcl, "errorInfo", NULL, TCL_GLOBAL_ONLY);
		if (infoObj) {
			event.data.compound["errorInfo"] = Data(Tcl_GetString(infoObj), Data::VERBATIM);
		}

		ctx->instance->returnEvent(event);
	}

	if (cmd)
		free(cmd);

	if (args) {
		for (int i = 0; i < nrArgs + 1; i++) {
			free(args[i]);
		}
		free(args);
	}

}

}