#include <string.h>
#include <stdlib.h> // malloc
#include <assert.h> // assert
#include <stdio.h>  // printf
#include <sstream> // stringstream
#include <deque> // deque
#include <boost/algorithm/string.hpp> // trim

#define USCXML_VERBOSE

#include "uscxml/config.h"

#ifdef APPLE
#include <mach/mach.h>
#include <mach/mach_time.h>
#include <pthread.h>
#endif

#ifndef AUTOINCLUDE_TEST
#include "test-c-machine.machine.c"
#endif

#include "uscxml/Convenience.h"
#include "uscxml/URL.h"
#include "uscxml/concurrency/Timer.h"
//#include "uscxml/DOMUtils.h"
#include "uscxml/Factory.h"
//#include "uscxml/Interpreter.h"
#include "uscxml/UUID.h"

#include "uscxml/concurrency/DelayedEventQueue.h"
#include "uscxml/concurrency/tinythread.h"

#ifdef BUILD_PROFILING
#   include "uscxml/plugins/DataModel.h"
# endif

#define USER_DATA(ctx) ((StateMachine*)(((uscxml_ctx*)ctx)->user_data))

using namespace uscxml;

class StateMachine : public InterpreterInfo {
public:
	StateMachine(const uscxml_machine* machine) : machine(machine), parentMachine(NULL), topMostMachine(NULL), invocation(NULL) {
		allMachines[sessionId] = this;
		topMostMachine = this;
		currentMachine = allMachines.begin();
		init();
	}

	StateMachine(StateMachine* parent, const uscxml_machine* machine, const uscxml_elem_invoke* invoke) : machine(machine), invocation(invoke) {
		parentMachine = parent;
		topMostMachine = parent->topMostMachine;
		init();
	}

	void init() {
		sessionId = UUID::getUUID();
		isFinalized = false;
		currEvent = NULL;

		// clear and initialize machine context
		memset(&ctx, 0, sizeof(uscxml_ctx));
		ctx.machine = machine;
		ctx.user_data = (void*)this;

		// register callbacks with scxml context
		ctx.is_enabled = &isEnabled;
		ctx.is_true = &isTrue;
		ctx.raise_done_event = &raiseDoneEvent;
		ctx.invoke = &invoke;
		ctx.exec_content_send = &execContentSend;
		ctx.exec_content_raise = &execContentRaise;
		ctx.exec_content_cancel = &execContentCancel;
		ctx.exec_content_log = &execContentLog;
		ctx.exec_content_assign = &execContentAssign;
		ctx.exec_content_foreach_init = &execContentForeachInit;
		ctx.exec_content_foreach_next = &execContentForeachNext;
		ctx.exec_content_foreach_done = &execContentForeachDone;
		ctx.dequeue_external = &dequeueExternal;
		ctx.dequeue_internal = &dequeueInternal;
		ctx.exec_content_init = &execContentInit;
		ctx.exec_content_script = &execContentScript;

		name = machine->name;

		delayQueue.start();
		dataModel = Factory::getInstance()->createDataModel(machine->datamodel, this);

		if (invocation != NULL) {
			/// test 226/240 - initialize from invoke request
			if (invocation->params != NULL) {
				const uscxml_elem_param* param = invocation->params;
				while(USCXML_ELEM_PARAM_IS_SET(param)) {
					std::string identifier;
					if (param->name != NULL) {
						identifier = param->name;
					} else if (param->location != NULL) {
						identifier = param->location;
					}
					invokeData[identifier] = parentMachine->dataModel.getStringAsData(param->expr);
					param++;
				}
			}

			if (invocation->namelist != NULL) {
				const char* cPtr = invocation->namelist;
				const char* aPtr = invocation->namelist;
				while(cPtr) {
					while (isspace(*cPtr))
						cPtr++;
					aPtr = cPtr;
					while(*cPtr && !isspace(*cPtr))
						cPtr++;

					if (aPtr == cPtr)
						break;

					std::string identifier = std::string(aPtr, cPtr - aPtr);
					invokeData[identifier] = parentMachine->dataModel.getStringAsData(identifier);
				}
			}
		}
	}

	virtual ~StateMachine() {
		if (parentMachine != NULL) {
			topMostMachine->allMachines.erase(topMostMachine->invocationIds[invocation]);
		}
//        finalize();

		delayQueue.stop();
		delayQueue.cancelAllEvents();

		while(eq.size() > 0) {
			delete eq.front();
			eq.pop_front();
		}
		eq.clear();
		while(iq.size() > 0) {
			delete iq.front();
			iq.pop_front();
		}
		iq.clear();
	}

	bool hasPendingWork() {
		return (iq.size() > 0 ||
		        eq.size() > 0 ||
		        ctx.flags & USCXML_CTX_SPONTANEOUS ||
		        ctx.flags == USCXML_CTX_PRISTINE ||
		        memcmp(ctx.config, ctx.invocations, sizeof(ctx.config)) != 0);
	}

	bool isDone() {
		return ctx.flags & USCXML_CTX_FINISHED;
	}

	void finalize() {
		if (isFinalized)
			return;

		delayQueue.stop();
		delayQueue.cancelAllEvents();

		if (parentMachine != NULL) {
			tthread::lock_guard<tthread::mutex> lock(mutex);

			Event* done = new Event();
			done->invokeid = invokeId;
			done->name = "done.invoke." + invokeId;
			parentMachine->eq.push_back(done);
		}
		isFinalized = true;
	}

	void reset() {
		delayQueue.stop();
		delayQueue.cancelAllEvents();

		while(eq.size() > 0) {
			delete eq.front();
			eq.pop_front();
		}
		while(iq.size() > 0) {
			delete iq.front();
			iq.pop_front();
		}

		iq.clear();
		eq.clear();

		init();

	}

	int step() {
		// advance current machine if there are multiple
		currentMachine++;
		if (currentMachine == allMachines.end())
			currentMachine = allMachines.begin();

		StateMachine* toRun = currentMachine->second;
		if (!toRun->hasPendingWork()) {
			return USCXML_ERR_IDLE;
		}

		// test 187
		if (toRun->isDone()) {
			toRun->finalize();
			return USCXML_ERR_IDLE;
		}

		state = uscxml_step(&toRun->ctx);
		if (toRun->currEvent != NULL) {
			delete toRun->currEvent;
			toRun->currEvent = NULL;
		}

		return state;
	}

	// InterpreterInfo
	NameSpaceInfo getNameSpaceInfo() const {
		return nsInfo;
	}
	const std::string& getName() {
		return name;
	}
	const std::string& getSessionId() {
		return sessionId;
	}
	const std::map<std::string, IOProcessor>& getIOProcessors() {
		return ioProcs;
	}
	const std::map<std::string, Invoker>& getInvokers() {
		return invokers;
	}
	Arabica::DOM::Document<std::string> getDocument() const {
		return document;
	}

	bool isInState(const std::string& stateId) {
		for (int i = 0 ; i < ctx.machine->nr_states; i++) {
			if (ctx.machine->states[i].name != NULL && BIT_HAS(i, ctx.config) && stateId == ctx.machine->states[i].name)
				return true;
		}
		return false;
	}

	// callbacks for scxml context

	static int isEnabled(const uscxml_ctx* ctx, const uscxml_transition* t, const void* e) {
		Event* event = (Event*)e;
		if (event == NULL) {
			if (t->event == NULL) {
				// spontaneous transition, null event
				if (t->condition != NULL)
					return isTrue(ctx, t->condition);
				return true;
			} else {
				// spontaneous transition, but real event
				return false;
			}
		}

		// real event but spontaneous transition
		if (t->event == NULL)
			return false;

		// real transition, real event
		if (nameMatch(t->event, event->name.c_str())) {
			if (t->condition != NULL)
				return isTrue(ctx, t->condition);
			return true;
		}
		return false;
	}

	static int isTrue(const uscxml_ctx* ctx, const char* expr) {
		try {
			return USER_DATA(ctx)->dataModel.evalAsBool(expr);
		} catch (Event e) {
			execContentRaise(ctx, e.name.c_str());
		}
		return false;
	}

	static int invoke(const uscxml_ctx* ctx, const uscxml_state* s, const uscxml_elem_invoke* invocation, unsigned char uninvoke) {
		std::map<std::string, StateMachine*> &allMachines = USER_DATA(ctx)->topMostMachine->allMachines;
		StateMachine* topMachine = USER_DATA(ctx)->topMostMachine;

		if (uninvoke) {
			if (invocation->machine != NULL) {
				if (topMachine->invocationIds.find(invocation) != topMachine->invocationIds.end() &&
				        allMachines.find(topMachine->invocationIds[invocation]) != allMachines.end()) {

					delete allMachines[topMachine->invocationIds[invocation]];
					topMachine->allMachines.erase(topMachine->invocationIds[invocation]);
					topMachine->invocationIds.erase(invocation);
				}
			} else {
				return USCXML_ERR_UNSUPPORTED;
			}
		} else {
			// invocations
			if (invocation->machine != NULL) {
				// invoke a nested SCXML machine
				StateMachine* invokedMachine = NULL;
				try {
					invokedMachine = new StateMachine(USER_DATA(ctx), invocation->machine, invocation);
				} catch (Event e) {
					delete invokedMachine;
					return USCXML_ERR_EXEC_CONTENT;
				}
				if (invocation->id != NULL) {
					invokedMachine->invokeId = invocation->id;
				} else if (invocation->idlocation != NULL) {
					// test224
					invokedMachine->invokeId = (invocation->sourcename != NULL ? std::string(invocation->sourcename) + "." : "") + UUID::getUUID();
					ctx->exec_content_assign(ctx, invocation->idlocation, std::string("\"" + invokedMachine->invokeId + "\"").c_str());
				} else {
					delete invokedMachine;
					return USCXML_ERR_UNSUPPORTED;
				}
				allMachines[invokedMachine->invokeId] = invokedMachine;
				topMachine->invocationIds[invocation] = invokedMachine->invokeId;
			} else {
				return USCXML_ERR_UNSUPPORTED;
			}
		}
		return USCXML_ERR_OK;
	}

	static int raiseDoneEvent(const uscxml_ctx* ctx, const uscxml_state* state, const uscxml_elem_donedata* donedata) {
		Event* e = new Event();
		e->name = std::string("done.state.") + state->name;

		if (donedata) {
			if (donedata->content != NULL) {
				e->data = Data(donedata->content, Data::VERBATIM);
			} else if (donedata->contentexpr != NULL) {
				try {
					e->data = USER_DATA(ctx)->dataModel.getStringAsData(donedata->contentexpr);
				} catch (Event e) {
					execContentRaise(ctx, e.name.c_str());
				}
			} else {
				try {
					const uscxml_elem_param* param = donedata->params;
					while (param && USCXML_ELEM_PARAM_IS_SET(param)) {
						Data paramValue;
						if (param->expr != NULL) {
							paramValue = USER_DATA(ctx)->dataModel.getStringAsData(param->expr);
						} else if(param->location) {
							paramValue = USER_DATA(ctx)->dataModel.getStringAsData(param->location);
						}
						e->params.insert(std::make_pair(param->name, paramValue));
						param++;
					}
				} catch (Event e) {
					execContentRaise(ctx, e.name.c_str());
				}
			}
		}

#ifdef USCXML_VERBOSE
		printf("Raising Done Event: %s\n", e->name.c_str());
#endif
		USER_DATA(ctx)->iq.push_back(e);
		return USCXML_ERR_OK;
	}

	static int execContentSend(const uscxml_ctx* ctx, const uscxml_elem_send* send) {
		SendRequest* e = new SendRequest();

		std::string target;
		if (send->target != NULL) {
			e->target = send->target;
		} else if (send->targetexpr != NULL) {
			e->target = USER_DATA(ctx)->dataModel.evalAsString(send->targetexpr);
		} else {
			e->target = "#_external";
		}

		if (e->target.size() > 0 && (e->target[0] != '#' || e->target[1] != '_')) {
			delete e;
			execContentRaise(ctx, "error.execution");
			return USCXML_ERR_INVALID_TARGET;
		}

		e->origintype = "http://www.w3.org/TR/scxml/#SCXMLEventProcessor";
		e->origin = e->target;

		try {
			if (send->type != NULL) {
				e->type = send->type;
			} else if (send->typeexpr != NULL) {
				e->type = USER_DATA(ctx)->dataModel.evalAsString(send->typeexpr);
			} else {
				e->type = "http://www.w3.org/TR/scxml/#SCXMLEventProcessor";
			}
		} catch (Event exc) {
			execContentRaise(ctx, exc.name.c_str());
			delete e;
			return USCXML_ERR_EXEC_CONTENT;
		}

		// only one somewhat supported
		if (e->type != "http://www.w3.org/TR/scxml/#SCXMLEventProcessor") {
			delete e;
			execContentRaise(ctx, "error.execution");
			return USCXML_ERR_INVALID_TARGET;
		}

		e->origintype = e->type;
		e->invokeid = USER_DATA(ctx)->invokeId;

		if (send->eventexpr != NULL) {
			e->name = USER_DATA(ctx)->dataModel.evalAsString(send->eventexpr);
		} else {
			e->name = send->event;
		}

		try {
			const uscxml_elem_param* param = send->params;
			while (param && USCXML_ELEM_PARAM_IS_SET(param)) {
				Data paramValue;
				if (param->expr != NULL) {
					paramValue = USER_DATA(ctx)->dataModel.getStringAsData(param->expr);
				} else if(param->location) {
					paramValue = USER_DATA(ctx)->dataModel.getStringAsData(param->location);
				}
				e->params.insert(std::make_pair(param->name, paramValue));
				param++;
			}
		} catch (Event e) {
			execContentRaise(ctx, e.name.c_str());
			return USCXML_ERR_EXEC_CONTENT;
		}

		try {
			if (send->namelist != NULL) {
				const char* bPtr = &send->namelist[0];
				const char* ePtr = bPtr;
				while(*ePtr != '\0') {
					ePtr++;
					if (*ePtr == ' ' || *ePtr == '\0') {
						std::string key(bPtr, ePtr - bPtr);
						e->params.insert(std::make_pair(key, USER_DATA(ctx)->dataModel.getStringAsData(key)));
						if (*ePtr == '\0')
							break;
						bPtr = ++ePtr;
					}
				}
			}
		} catch (Event e) {
			execContentRaise(ctx, e.name.c_str());
			return USCXML_ERR_EXEC_CONTENT;
		}

		if (send->content != NULL) {
			// will it parse as json?
			Data d = Data::fromJSON(send->content);
			if (!d.empty()) {
				e->data = d;
			} else {
				e->data = Data(spaceNormalize(send->content), Data::VERBATIM);
			}
		}

		std::string sendid;
		if (send->id != NULL) {
			sendid = send->id;
			e->sendid = sendid;
		} else {
			sendid = UUID::getUUID();
			if (send->idlocation != NULL) {
				USER_DATA(ctx)->dataModel.assign(send->idlocation, Data(sendid, Data::VERBATIM));
			} else {
				e->hideSendId = true;
			}
		}

		size_t delayMs = 0;
		std::string delay;
		if (send->delayexpr != NULL) {
			delay = USER_DATA(ctx)->dataModel.evalAsString(send->delayexpr);
		} else if (send->delay != NULL) {
			delay = send->delay;
		}
		if (delay.size() > 0) {
			boost::trim(delay);

			NumAttr delayAttr(delay);
			if (iequals(delayAttr.unit, "ms")) {
				delayMs = strTo<uint32_t>(delayAttr.value);
			} else if (iequals(delayAttr.unit, "s")) {
				delayMs = strTo<double>(delayAttr.value) * 1000;
			} else if (delayAttr.unit.length() == 0) { // unit less delay is interpreted as milliseconds
				delayMs = strTo<uint32_t>(delayAttr.value);
			} else {
				std::cerr << "Cannot make sense of delay value " << delay << ": does not end in 's' or 'ms'";
			}
		}

		if (USER_DATA(ctx)->invokeId.size() > 0) {
			e->invokeid = USER_DATA(ctx)->invokeId;
		}

		USER_DATA(ctx)->sendIds[sendid] = e;
		if (delayMs > 0) {
			USER_DATA(ctx)->delayQueue.addEvent(sendid, delayedSend, delayMs, (void*)ctx);
		} else {
			delayedSend((void*)ctx, sendid);
		}

		return USCXML_ERR_OK;
	}

	static int execContentRaise(const uscxml_ctx* ctx, const char* event) {
		Event* e = new Event();
		e->name = event;

		if (boost::starts_with(e->name, "error.")) {
			e->eventType = Event::PLATFORM;
		} else {
			e->eventType = Event::INTERNAL;
		}
		USER_DATA(ctx)->iq.push_back(e);
		return USCXML_ERR_OK;
	}

	static int execContentCancel(const uscxml_ctx* ctx, const char* sendid, const char* sendidexpr) {
		std::string eventId;
		if (sendid != NULL) {
			eventId = sendid;
		} else if (sendidexpr != NULL) {
			eventId = USER_DATA(ctx)->dataModel.evalAsString(sendidexpr);
		}

		if (eventId.length() > 0) {
			USER_DATA(ctx)->delayQueue.cancelEvent(eventId);
		} else {
			execContentRaise(ctx, "error.execution");
			return USCXML_ERR_EXEC_CONTENT;
		}
		return USCXML_ERR_OK;
	}

	static int execContentLog(const uscxml_ctx* ctx, const char* label, const char* expr) {
		try {
			if (label != NULL) {
				printf("%s%s", label, (expr != NULL ? ": " : ""));
			}
			if (expr != NULL) {
				std::string msg = USER_DATA(ctx)->dataModel.evalAsString(expr);
				printf("%s", msg.c_str());
			}
			if (label != NULL || expr != NULL) {
				printf("\n");
			}
		} catch (Event e) {
			execContentRaise(ctx, e.name.c_str());
			return USCXML_ERR_EXEC_CONTENT;
		}
		return USCXML_ERR_OK;
	}

	static int execContentAssign(const uscxml_ctx* ctx, const char* location, const char* expr) {
		std::string key = location;
		if (key == "_sessionid" || key == "_name" || key == "_ioprocessors" || key == "_invokers" || key == "_event") {
			execContentRaise(ctx, "error.execution");
			return USCXML_ERR_EXEC_CONTENT;
		}

		try {
			Data d = USER_DATA(ctx)->dataModel.getStringAsData(expr);
			USER_DATA(ctx)->dataModel.assign(key, d);
		} catch (Event e) {
			execContentRaise(ctx, e.name.c_str());
			return USCXML_ERR_EXEC_CONTENT;
		}
		return USCXML_ERR_OK;
	}

	static int execContentForeachInit(const uscxml_ctx* ctx, const uscxml_elem_foreach* foreach) {
		try {
			scxml_foreach_info* feInfo = (scxml_foreach_info*)malloc(sizeof(scxml_foreach_info));
			USER_DATA(ctx)->foreachInfo[foreach] = feInfo;

			feInfo->iterations = USER_DATA(ctx)->dataModel.getLength(foreach->array);
			feInfo->currIteration = 0;
		} catch (Event e) {
			execContentRaise(ctx, e.name.c_str());
			return USCXML_ERR_EXEC_CONTENT;
		}
		return USCXML_ERR_OK;
	}

	static int execContentForeachNext(const uscxml_ctx* ctx, const uscxml_elem_foreach* foreach) {
		try {
			scxml_foreach_info* feInfo = USER_DATA(ctx)->foreachInfo[foreach];
			if (feInfo->currIteration < feInfo->iterations) {
				USER_DATA(ctx)->dataModel.setForeach((foreach->item != NULL ? foreach->item : ""),
				                                     (foreach->array != NULL ? foreach->array : ""),
				                                     (foreach->index != NULL ? foreach->index : ""),
				                                     feInfo->currIteration);
				feInfo->currIteration++;
				return USCXML_ERR_OK;
			}
		} catch (Event e) {
			execContentRaise(ctx, e.name.c_str());
			free(USER_DATA(ctx)->foreachInfo[foreach]);
			USER_DATA(ctx)->foreachInfo.erase(foreach);
			return USCXML_ERR_EXEC_CONTENT;
		}
		return USCXML_ERR_FOREACH_DONE;
	}

	static int execContentForeachDone(const uscxml_ctx* ctx, const uscxml_elem_foreach* foreach) {
		free(USER_DATA(ctx)->foreachInfo[foreach]);
		USER_DATA(ctx)->foreachInfo.erase(foreach);
		return USCXML_ERR_OK;
	}

	static int execContentInit(const uscxml_ctx* ctx, const uscxml_elem_data* data) {
		while(USCXML_ELEM_DATA_IS_SET(data)) {
			if (USER_DATA(ctx)->invokeData.find(data->id) != USER_DATA(ctx)->invokeData.end()) {
				// passed via param or namelist: test245
				try {
					USER_DATA(ctx)->dataModel.init(data->id, USER_DATA(ctx)->invokeData[data->id]);
				} catch (Event e) {
					execContentRaise(ctx, e.name.c_str());
				}
			} else {
				Data d;
				std::stringstream content;

				if (data->expr != NULL) {
					d = USER_DATA(ctx)->dataModel.getStringAsData(data->expr);
//					d = Data(data->expr, Data::INTERPRETED);
				} else if (data->content != NULL) {
					content << data->content;
					d = USER_DATA(ctx)->dataModel.getStringAsData(content.str());
//					d = Data(content.str(), Data::INTERPRETED);
				} else if (data->src != NULL) {
					URL sourceURL(data->src);
					if (USER_DATA(ctx)->baseURL.size() > 0) {
						sourceURL.toAbsolute(USER_DATA(ctx)->baseURL);
					} else {
						sourceURL.toAbsoluteCwd();
					}
					content << sourceURL;
//					d = Data(content.str(), Data::INTERPRETED);
					d = USER_DATA(ctx)->dataModel.getStringAsData(content.str());
				} else {
					d = Data("undefined", Data::INTERPRETED);
				}
				try {
					// this might fail with an unquoted string literal in content
					USER_DATA(ctx)->dataModel.init(data->id, d);
				} catch (Event e) {
					if (content.str().size() > 0) {
						try {
							d = Data(escape(spaceNormalize(content.str())), Data::VERBATIM);
							USER_DATA(ctx)->dataModel.init(data->id, d);
						} catch (Event e) {
							execContentRaise(ctx, e.name.c_str());
						}
					} else {
						execContentRaise(ctx, e.name.c_str());
					}
				}
			}
			data++;
		}
		return USCXML_ERR_OK;
	}

	static int execContentScript(const uscxml_ctx* ctx, const char* src, const char* content) {
		if (content != NULL) {
			USER_DATA(ctx)->dataModel.eval(Arabica::DOM::Element<std::string>(), content);
		} else if (src != NULL) {
			return USCXML_ERR_UNSUPPORTED;
		}
		return USCXML_ERR_OK;
	}

	static void* dequeueExternal(const uscxml_ctx* ctx) {
		tthread::lock_guard<tthread::mutex> lock(USER_DATA(ctx)->mutex);
		if (USER_DATA(ctx)->eq.size() == 0)
			return NULL;

		Event* e = USER_DATA(ctx)->eq.front();
		USER_DATA(ctx)->eq.pop_front();
		USER_DATA(ctx)->currEvent = e;
		USER_DATA(ctx)->dataModel.setEvent(*e);

		std::map<std::string, StateMachine*>& allMachines = USER_DATA(ctx)->topMostMachine->allMachines;
		if (e->invokeid.size() > 0 && allMachines.find(e->invokeid) != allMachines.end()) {
			// we need to check for finalize content
			StateMachine* invokedMachine = allMachines[e->invokeid];
			if (invokedMachine->invocation != NULL && invokedMachine->invocation->finalize != NULL)
				invokedMachine->invocation->finalize(ctx,
				                                     invokedMachine->invocation,
				                                     e);
		}

		// auto forward event
		for (std::map<std::string, StateMachine*>::iterator machIter = allMachines.begin(); machIter != allMachines.end(); machIter++) {
			if (machIter->second->parentMachine != NULL &&
			        machIter->second->parentMachine == USER_DATA(ctx) &&
			        machIter->second->invocation->autoforward) {
				tthread::lock_guard<tthread::mutex> lock(machIter->second->mutex);

				Event* ne = new Event(*e);
				machIter->second->eq.push_back(ne);
			}
		}

#ifdef USCXML_VERBOSE
		printf("Popping External Event: %s\n", e->name.c_str());
#endif
		return e;
	}

	static void* dequeueInternal(const uscxml_ctx* ctx) {
		if (USER_DATA(ctx)->iq.size() == 0)
			return NULL;
		Event* e = USER_DATA(ctx)->iq.front();
		USER_DATA(ctx)->iq.pop_front();
		USER_DATA(ctx)->currEvent = e;
		USER_DATA(ctx)->dataModel.setEvent(*e);
#ifdef USCXML_VERBOSE
		printf("Popping Internal Event: %s\n", e->name.c_str());
#endif
		return e;
	}

	static void delayedSend(void* ctx, std::string eventName) {
		tthread::lock_guard<tthread::mutex> lock(USER_DATA(ctx)->mutex);

		SendRequest* sr = USER_DATA(ctx)->sendIds[eventName];
		Event* e = new Event(*sr);

		if (sr->target == "#_internal") {
			e->eventType = Event::INTERNAL;
#ifdef USCXML_VERBOSE
			printf("Pushing Internal Event: %s\n", e->name.c_str());
#endif
			USER_DATA(ctx)->iq.push_back(e);
		} else if (sr->target == "#_external") {
			e->eventType = Event::EXTERNAL;
#ifdef USCXML_VERBOSE
			printf("Pushing External Event: %s\n", e->name.c_str());
#endif
			USER_DATA(ctx)->eq.push_back(e);
		} else if (sr->target == "#_parent") {
			e->eventType = Event::EXTERNAL;
			if (USER_DATA(ctx)->parentMachine != NULL) {
				USER_DATA(ctx)->parentMachine->eq.push_back(e);
			}
			// TODO: handle invalid parent
		} else if (sr->target.substr(0,8) == "#_scxml_") {
			std::string sessionId = sr->target.substr(8);
			bool sessionFound = false;
			for (std::map<std::string, StateMachine*>::iterator machIter = USER_DATA(ctx)->topMostMachine->allMachines.begin();
			        machIter != USER_DATA(ctx)->topMostMachine->allMachines.end(); machIter++) {
				if (machIter->second->sessionId == sessionId) {
					e->eventType = Event::EXTERNAL;
					machIter->second->eq.push_back(e);
					sessionFound = true;
					break;
				}
			}
			if (!sessionFound) {
				// test496
				execContentRaise((uscxml_ctx*)ctx, "error.communication");
			}
		} else if (sr->target.substr(0,2) == "#_") {
			e->eventType = Event::EXTERNAL;
			std::string targetId = sr->target.substr(2);
			if (USER_DATA(ctx)->topMostMachine->allMachines.find(targetId) != USER_DATA(ctx)->topMostMachine->allMachines.end()) {
				USER_DATA(ctx)->topMostMachine->allMachines[targetId]->eq.push_back(e);
			} else {
				execContentRaise((uscxml_ctx*)ctx, "error.communication");
			}
		} else {
			assert(false);
		}
		USER_DATA(ctx)->monitor.notify_all();
		delete sr;
	}

	static std::string spaceNormalize(const std::string& text) {
		std::stringstream content;
		std::string seperator;

		size_t start = 0;
		for (int i = 0; i < text.size(); i++) {
			if (isspace(text[i])) {
				if (i > 0 && start < i) {
					content << seperator << text.substr(start, i - start);
					seperator = " ";
				}
				while(isspace(text[++i])); // skip whitespaces
				start = i;
			} else if (i + 1 == text.size()) {
				content << seperator << text.substr(start, i + 1 - start);
			}
		}
		return content.str();
	}

	// TODO: isolate InterpreterImpl to reduce header deps on libxml/parser.h
	static bool nameMatch(const std::string& eventDescs, const std::string& eventName) {
		if(eventDescs.length() == 0 || eventName.length() == 0)
			return false;

		// naive case of single descriptor and exact match
		if (iequals(eventDescs, eventName))
			return true;

		size_t start = 0;
		std::string eventDesc;
		for (int i = 0; i < eventDescs.size(); i++) {
			if (isspace(eventDescs[i])) {
				if (i > 0 && start < i - 1) {
					eventDesc = eventDescs.substr(start, i - start);
				}
				while(isspace(eventDescs[++i])); // skip whitespaces
				start = i;
			} else if (i + 1 == eventDescs.size()) {
				eventDesc = eventDescs.substr(start, i + 1 - start);
			}

			if (eventDesc.size() > 0) {
				// remove optional trailing .* for CCXML compatibility
				if (eventDesc.find("*", eventDesc.size() - 1) != std::string::npos)
					eventDesc = eventDesc.substr(0, eventDesc.size() - 1);
				if (eventDesc.find(".", eventDesc.size() - 1) != std::string::npos)
					eventDesc = eventDesc.substr(0, eventDesc.size() - 1);

				// was eventDesc the * wildcard
				if (eventDesc.size() == 0)
					return true;

				// eventDesc has to be a real prefix of event now and therefore shorter
				if (eventDesc.size() > eventName.size())
					goto NEXT_DESC;

				// are they already equal?
				if (iequals(eventDesc, eventName))
					return true;

				if (eventName.find(eventDesc) == 0) {
					if (eventName.find(".", eventDesc.size()) == eventDesc.size())
						return true;
				}
NEXT_DESC:
				eventDesc = "";
			}
		}
		return false;
	}

	Event* currEvent;

	std::map<const uscxml_elem_invoke*, std::string> invocationIds;
	std::map<std::string, StateMachine*> allMachines;

	bool isFinalized;
	int state;
	uscxml_ctx ctx;
	const uscxml_machine* machine;

	StateMachine* parentMachine;
	StateMachine* topMostMachine;
	std::map<std::string, StateMachine* >::iterator currentMachine; // next machine to advance

	std::string baseURL;
	std::string sessionId;
	std::string name;

	// in case we were invoked
	std::string invokeId;
	const uscxml_elem_invoke* invocation;
	std::map<std::string, Data> invokeData;

	std::deque<Event*> iq;
	std::deque<Event*> eq;

	DataModel dataModel;

protected:
	struct scxml_foreach_info {
		size_t iterations;
		size_t currIteration;
	};

	NameSpaceInfo nsInfo;
	std::map<std::string, IOProcessor> ioProcs;
	std::map<std::string, Invoker> invokers;
	Arabica::DOM::Document<std::string> document;

	DelayedEventQueue delayQueue;
	std::map<std::string, SendRequest*> sendIds;
	std::map<const uscxml_elem_foreach*, scxml_foreach_info*> foreachInfo;

	tthread::condition_variable monitor;
	tthread::mutex mutex;
};


int main(int argc, char** argv) {

	int err;
	size_t benchmarkRuns = 1;
	const char* envBenchmarkRuns = getenv("USCXML_BENCHMARK_ITERATIONS");
	if (envBenchmarkRuns != NULL) {
		benchmarkRuns = strTo<size_t>(envBenchmarkRuns);
	}

	size_t remainingRuns = benchmarkRuns;

	double avg = 0;
	size_t microSteps = 0;
#ifdef BUILD_PROFILING
	double avgDm = 0;
#endif

	StateMachine rootMachine(&uscxml_machines[0]);

	Timer tTotal;
	tTotal.start();
	while(remainingRuns-- > 0) {

		Timer t;
		t.start();
		microSteps = 0;


		for (;;) {
			err = rootMachine.step();
			if (rootMachine.isDone())
				break;
			t.stop();
			microSteps++;

			t.start();
		}
		microSteps++;

		assert(rootMachine.ctx.flags & USCXML_CTX_TOP_LEVEL_FINAL);
		t.stop();

		avg += t.elapsed;
#ifdef BUILD_PROFILING
		avgDm += rootMachine.dataModel.timer.elapsed;
		rootMachine.dataModel.timer.elapsed = 0;
#endif
		size_t passIdx = 0;
		for (int i = 0; i < rootMachine.ctx.machine->nr_states; i++) {
			if (rootMachine.ctx.machine->states[i].name && strcmp(rootMachine.ctx.machine->states[i].name, "pass") == 0) {
				passIdx = i;
				break;
			}
		}

		if(!BIT_HAS(passIdx, rootMachine.ctx.config)) {
			std::cerr << "Interpreter did not end in pass" << std::endl;
			exit(EXIT_FAILURE);
		}
		rootMachine.reset();
	}
	tTotal.stop();
	std::cout << benchmarkRuns << " iterations" << std::endl;
	std::cout << tTotal.elapsed * 1000.0 << " ms in total" << std::endl;
	std::cout << (avg * 1000.0) / (double)benchmarkRuns << " ms per execution" << std::endl;
	std::cout << microSteps << " microsteps per iteration" << std::endl;
	std::cout << (avg * 1000.0) / ((double)benchmarkRuns * (double)microSteps) << " ms per microstep" << std::endl;
#ifdef BUILD_PROFILING
	std::cout << (avgDm * 1000.0) / (double)benchmarkRuns << " ms in dataModel" << std::endl;
	std::cout << ((avg - avgDm) * 1000.0) / ((double)benchmarkRuns * (double)microSteps) << " ms per microstep \\wo dataModel" << std::endl;
#endif
	tthread::this_thread::sleep_for(tthread::chrono::milliseconds(100));
	return EXIT_SUCCESS;
}
