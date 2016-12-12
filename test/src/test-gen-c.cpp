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
#include "test-c-machine.scxml.c"
//#include "/Users/sradomski/Documents/TK/Code/uscxml/build/cli/test/gen/c/ecma/test329.scxml.machine.c"
#endif

#include "uscxml/util/URL.h"
//#include "uscxml/concurrency/Timer.h"
//#include "uscxml/dom/DOMUtils.h"
#include "uscxml/plugins/Factory.h"
//#include "uscxml/Interpreter.h"
#include "uscxml/util/UUID.h"

#include "uscxml/interpreter/InterpreterImpl.h"
#include "uscxml/interpreter/BasicEventQueue.h"
#include "uscxml/interpreter/BasicDelayedEventQueue.h"

#ifdef BUILD_PROFILING
#   include "uscxml/plugins/DataModel.h"
# endif

#define USER_DATA(ctx) ((StateMachine*)(((uscxml_ctx*)ctx)->user_data))

using namespace uscxml;

class StateMachine : public DataModelCallbacks, public DelayedEventQueueCallbacks {
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

	virtual Logger getLogger() {
		return Logger::getDefault();
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

	bool isInState(const std::string& stateId) {
		for (size_t i = 0; i < ctx.machine->nr_states; i++) {
			if (ctx.machine->states[i].name &&
			        strcmp(ctx.machine->states[i].name, stateId.c_str()) == 0 &&
			        BIT_HAS(i, ctx.config)) {

				return true;
			}
		}

		return false;
	}

	XERCESC_NS::DOMDocument* getDocument() const {
		return document;
	}
	const std::map<std::string, Invoker>& getInvokers() {
		return invokers;
	}

	void init() {
		sessionId = uscxml::UUID::getUUID();
		isFinalized = false;

		// clear and initialize machine context
		memset(&ctx, 0, sizeof(uscxml_ctx));
		ctx.machine = machine;
		ctx.user_data = (void*)this;

		// register callbacks with scxml context
		ctx.is_matched = &isMatched;
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

		delayQueue = DelayedEventQueue(std::shared_ptr<DelayedEventQueueImpl>(new BasicDelayedEventQueue(this)));
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
					invokeData[identifier] = parentMachine->dataModel.evalAsData(param->expr);
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
					invokeData[identifier] = parentMachine->dataModel.evalAsData(identifier);
				}
			}
		}
	}

	virtual ~StateMachine() {
		if (parentMachine != NULL) {
			topMostMachine->allMachines.erase(topMostMachine->invocationIds[invocation]);
		}
//        finalize();

		delayQueue.cancelAllDelayed();

		while(eq.size() > 0) {
			eq.pop_front();
		}
		eq.clear();
		while(iq.size() > 0) {
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

		delayQueue.cancelAllDelayed();

		if (parentMachine != NULL) {
			std::lock_guard<std::mutex> lock(mutex);

			Event done;
			done.invokeid = invokeId;
			done.name = "done.invoke." + invokeId;
			parentMachine->eq.push_back(done);
		}
		isFinalized = true;
	}

	void reset() {
		delayQueue.cancelAllDelayed();

		while(eq.size() > 0) {
			eq.pop_front();
		}
		while(iq.size() > 0) {
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
		return state;
	}

	// callbacks for scxml context

	static int isMatched(const uscxml_ctx* ctx, const uscxml_transition* t, const void* e) {
		Event* event = (Event*)e;
		return (nameMatch(t->event, event->name.c_str()));
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
					invokedMachine->invokeId = (invocation->sourcename != NULL ? std::string(invocation->sourcename) + "." : "") + uscxml::UUID::getUUID();
					USER_DATA(ctx)->dataModel.assign(invocation->idlocation, Data(invokedMachine->invokeId, Data::VERBATIM));
				} else {
					invokedMachine->invokeId = uscxml::UUID::getUUID();
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
		Event e;
		e.name = std::string("done.state.") + state->name;

		if (donedata) {
			if (donedata->content != NULL) {
				e.data = Data(donedata->content, Data::VERBATIM);
			} else if (donedata->contentexpr != NULL) {
				try {
					e.data = USER_DATA(ctx)->dataModel.getAsData(donedata->contentexpr);
				} catch (Event e) {
					execContentRaise(ctx, e.name.c_str());
				}
			} else {
				try {
					const uscxml_elem_param* param = donedata->params;
					while (param && USCXML_ELEM_PARAM_IS_SET(param)) {
						Data paramValue;
						if (param->expr != NULL) {
							paramValue = USER_DATA(ctx)->dataModel.evalAsData(param->expr);
						} else if(param->location) {
							paramValue = USER_DATA(ctx)->dataModel.evalAsData(param->location);
						}
						e.params.insert(std::make_pair(param->name, paramValue));
						param++;
					}
				} catch (Event e) {
					execContentRaise(ctx, e.name.c_str());
				}
			}
		}

#ifdef USCXML_VERBOSE
		printf("Raising Done Event: %s\n", e.name.c_str());
#endif
		USER_DATA(ctx)->iq.push_back(e);
		return USCXML_ERR_OK;
	}

	static int execContentSend(const uscxml_ctx* ctx, const uscxml_elem_send* send) {
		Event e;

		std::string sendid;
		if (send->id != NULL) {
			sendid = send->id;
		} else {
			sendid = uscxml::UUID::getUUID();
			if (send->idlocation != NULL) {
				USER_DATA(ctx)->dataModel.assign(send->idlocation, Data(sendid, Data::VERBATIM));
			} else {
				e.hideSendId = true;
			}
		}
		e.sendid = sendid;

		std::string target;
		if (send->target != NULL) {
			target = send->target;
		} else if (send->targetexpr != NULL) {
			target = USER_DATA(ctx)->dataModel.evalAsData(send->targetexpr).atom;
		} else {
			target = "#_external";
		}

		if (target.size() > 0 && (target[0] != '#' || target[1] != '_')) {
			e.name = "error.execution";
			execContentRaise(ctx, e);
			return USCXML_ERR_INVALID_TARGET;
		}

		e.origintype = "http://www.w3.org/TR/scxml/#SCXMLEventProcessor";
//		e.origin = target;

		std::string type;
		try {
			if (send->type != NULL) {
				type = send->type;
			} else if (send->typeexpr != NULL) {
				type = USER_DATA(ctx)->dataModel.evalAsData(send->typeexpr).atom;
			} else {
				type = "http://www.w3.org/TR/scxml/#SCXMLEventProcessor";
			}
		} catch (Event exc) {
			e.name = "error.execution";
			execContentRaise(ctx, e);
			return USCXML_ERR_EXEC_CONTENT;
		}

		// only one somewhat supported
		if (type != "http://www.w3.org/TR/scxml/#SCXMLEventProcessor") {
			e.name = "error.execution";
			execContentRaise(ctx, e);
			return USCXML_ERR_INVALID_TARGET;
		}

		e.origintype = type;
		e.invokeid = USER_DATA(ctx)->invokeId;

		if (send->eventexpr != NULL) {
			e.name = USER_DATA(ctx)->dataModel.evalAsData(send->eventexpr).atom;
		} else {
			e.name = send->event;
		}

		try {
			const uscxml_elem_param* param = send->params;
			while (param && USCXML_ELEM_PARAM_IS_SET(param)) {
				Data paramValue;
				if (param->expr != NULL) {
					paramValue = USER_DATA(ctx)->dataModel.evalAsData(param->expr);
				} else if(param->location) {
					paramValue = USER_DATA(ctx)->dataModel.evalAsData(param->location);
				}
				e.params.insert(std::make_pair(param->name, paramValue));
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
						e.params.insert(std::make_pair(key, USER_DATA(ctx)->dataModel.evalAsData(key)));
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
			Data d = USER_DATA(ctx)->dataModel.getAsData(send->content);
			if (!d.empty()) {
				e.data = d;
			} else {
				e.data = Data(spaceNormalize(send->content), Data::VERBATIM);
			}
		}

		size_t delayMs = 0;
		std::string delay;
		if (send->delayexpr != NULL) {
			delay = USER_DATA(ctx)->dataModel.evalAsData(send->delayexpr).atom;
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
			e.invokeid = USER_DATA(ctx)->invokeId;
		}

		USER_DATA(ctx)->sendUUIDs[e.uuid] = std::make_tuple(e.sendid, target, type);
		if (delayMs > 0) {
			USER_DATA(ctx)->delayQueue.enqueueDelayed(e, delayMs, e.uuid);
		} else {
			USER_DATA(ctx)->eventReady(e, e.uuid);
		}

		return USCXML_ERR_OK;
	}

	static int execContentRaise(const uscxml_ctx* ctx, Event& e) {
		if (boost::starts_with(e.name, "error.")) {
			e.eventType = Event::PLATFORM;
		} else {
			e.eventType = Event::INTERNAL;
		}
		USER_DATA(ctx)->iq.push_back(e);
		return USCXML_ERR_OK;
	}

	static int execContentRaise(const uscxml_ctx* ctx, const char* event) {
		Event e;
		e.name = event;
		return execContentRaise(ctx, e);
	}

	static int execContentCancel(const uscxml_ctx* ctx, const char* sendid, const char* sendidexpr) {
		std::string eventId;
		if (sendid != NULL) {
			eventId = sendid;
		} else if (sendidexpr != NULL) {
			eventId = USER_DATA(ctx)->dataModel.evalAsData(sendidexpr).atom;
		}

		if (eventId.length() > 0) {
			// find all events with given id
			for (auto evIter = USER_DATA(ctx)->sendUUIDs.begin(); evIter != USER_DATA(ctx)->sendUUIDs.end(); evIter++) {
				std::string sendid = std::get<0>(evIter->second);
				if (eventId == sendid) {
					USER_DATA(ctx)->delayQueue.cancelDelayed(evIter->first);
				}
			}

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
				std::string msg = USER_DATA(ctx)->dataModel.evalAsData(expr).atom;
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

	static int execContentAssign(const uscxml_ctx* ctx, const uscxml_elem_assign* assign) {
		std::string key = assign->location;
		if (key == "_sessionid" || key == "_name" || key == "_ioprocessors" || key == "_invokers" || key == "_event") {
			execContentRaise(ctx, "error.execution");
			return USCXML_ERR_EXEC_CONTENT;
		}

		try {
//			Data d = USER_DATA(ctx)->dataModel.getStringAsData(expr);
			if (assign->expr != NULL) {
				USER_DATA(ctx)->dataModel.assign(key,
				                                 USER_DATA(ctx)->dataModel.evalAsData(assign->expr));
			} else if (assign->content != NULL) {
				Data d = Data(assign->content, Data::INTERPRETED);
				USER_DATA(ctx)->dataModel.assign(key, d);
			}
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

				try {
					if (data->expr != NULL) {
						d = USER_DATA(ctx)->dataModel.evalAsData(data->expr);

					} else if (data->content != NULL || data->src != NULL) {
						if (data->content) {
							content << data->content;
						} else {
							URL sourceURL(data->src);
							if (USER_DATA(ctx)->baseURL.size() > 0) {
								sourceURL = URL::resolve(sourceURL, USER_DATA(ctx)->baseURL);
							} else {
								sourceURL = URL::resolveWithCWD(sourceURL);
							}
							content << sourceURL.getInContent();
						}
						/**
						 * first attempt to parse as structured data, we will try
						 * as space normalized string literals if this fails below
						 */
						d = USER_DATA(ctx)->dataModel.getAsData(content.str());

					} else {
						// leave d undefined
					}
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
			USER_DATA(ctx)->dataModel.evalAsData(content);
		} else if (src != NULL) {
			return USCXML_ERR_UNSUPPORTED;
		}
		return USCXML_ERR_OK;
	}

	static void* dequeueExternal(const uscxml_ctx* ctx) {
		std::lock_guard<std::mutex> lock(USER_DATA(ctx)->mutex);
		if (USER_DATA(ctx)->eq.size() == 0)
			return NULL;

		// set event
		USER_DATA(ctx)->currEvent = USER_DATA(ctx)->eq.front();
		USER_DATA(ctx)->eq.pop_front();

		// get an alias
		const Event& e = USER_DATA(ctx)->currEvent;
		USER_DATA(ctx)->dataModel.setEvent(e);

		std::map<std::string, StateMachine*>& allMachines = USER_DATA(ctx)->topMostMachine->allMachines;
		if (e.invokeid.size() > 0 && allMachines.find(e.invokeid) != allMachines.end()) {
			// we need to check for finalize content
			StateMachine* invokedMachine = allMachines[e.invokeid];
			if (invokedMachine->invocation != NULL && invokedMachine->invocation->finalize != NULL)
				invokedMachine->invocation->finalize(ctx,
				                                     invokedMachine->invocation,
				                                     &e);
		}

		// auto forward event
		for (std::map<std::string, StateMachine*>::iterator machIter = allMachines.begin(); machIter != allMachines.end(); machIter++) {
			if (machIter->second->parentMachine != NULL &&
			        machIter->second->parentMachine == USER_DATA(ctx) &&
			        machIter->second->invocation->autoforward) {
				std::lock_guard<std::mutex> lock(machIter->second->mutex);

				Event e2(e);
				machIter->second->eq.push_back(e2);
			}
		}

#ifdef USCXML_VERBOSE
		printf("Popping External Event: %s\n", e.name.c_str());
#endif
		return &USER_DATA(ctx)->currEvent;
	}

	static void* dequeueInternal(const uscxml_ctx* ctx) {
		if (USER_DATA(ctx)->iq.size() == 0)
			return NULL;
		// set event
		USER_DATA(ctx)->currEvent = USER_DATA(ctx)->iq.front();
		USER_DATA(ctx)->iq.pop_front();

		// get an alias
		const Event& e = USER_DATA(ctx)->currEvent;
		USER_DATA(ctx)->dataModel.setEvent(e);

#ifdef USCXML_VERBOSE
		printf("Popping Internal Event: %s\n", e.name.c_str());
#endif
		return &USER_DATA(ctx)->currEvent;
	}

	void eventReady(Event& e, const std::string& eventUUID) {
		std::lock_guard<std::mutex> lock(mutex);

		//std::make_tuple(e.sendid, target, type);

		std::string sendid = std::get<0>(sendUUIDs[e.uuid]);
		std::string target = std::get<1>(sendUUIDs[e.uuid]);
		std::string type = std::get<2>(sendUUIDs[e.uuid]);

		if (target == "#_internal") {
			e.eventType = Event::INTERNAL;
#ifdef USCXML_VERBOSE
			printf("Pushing Internal Event: %s\n", e.name.c_str());
#endif
			iq.push_back(e);
		} else if (target == "#_external") {
			e.eventType = Event::EXTERNAL;
#ifdef USCXML_VERBOSE
			printf("Pushing External Event: %s\n", e.name.c_str());
#endif
			eq.push_back(e);
		} else if (target == "#_parent") {
			e.eventType = Event::EXTERNAL;
			if (parentMachine != NULL) {
				parentMachine->eq.push_back(e);
			}
			// TODO: handle invalid parent
		} else if (target.substr(0,8) == "#_scxml_") {
			std::string sessionId = target.substr(8);
			bool sessionFound = false;
			for (std::map<std::string, StateMachine*>::iterator machIter = topMostMachine->allMachines.begin();
			        machIter != topMostMachine->allMachines.end(); machIter++) {
				if (machIter->second->sessionId == sessionId) {
					e.eventType = Event::EXTERNAL;
					machIter->second->eq.push_back(e);
					sessionFound = true;
					break;
				}
			}
			if (!sessionFound) {
				// test496
				execContentRaise(&ctx, "error.communication");
			}
		} else if (target.substr(0,2) == "#_") {
			e.eventType = Event::EXTERNAL;
			std::string targetId = target.substr(2);
			if (topMostMachine->allMachines.find(targetId) != topMostMachine->allMachines.end()) {
				topMostMachine->allMachines[targetId]->eq.push_back(e);
			} else {
				execContentRaise(&ctx, "error.communication");
			}
		} else {
			assert(false);
		}
		monitor.notify_all();
	}

	static std::string spaceNormalize(const std::string& text) {
		std::stringstream content;
		std::string seperator;

		size_t start = 0;
		for (size_t i = 0; i < text.size(); i++) {
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
		for (size_t i = 0; i < eventDescs.size(); i++) {
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

	Event currEvent;

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

	std::deque<Event> iq;
	std::deque<Event> eq;

	DataModel dataModel;

protected:
	struct scxml_foreach_info {
		size_t iterations;
		size_t currIteration;
	};

	X xmlPrefix;
	std::map<std::string, IOProcessor> ioProcs;
	std::map<std::string, Invoker> invokers;
	XERCESC_NS::DOMDocument* document;

	DelayedEventQueue delayQueue;
	std::map<std::string, std::tuple<std::string, std::string, std::string> > sendUUIDs;
	std::map<const uscxml_elem_foreach*, scxml_foreach_info*> foreachInfo;

	std::condition_variable monitor;
	std::mutex mutex;
};


int main(int argc, char** argv) {

	int err;
	size_t benchmarkRuns = 1;
	const char* envBenchmarkRuns = getenv("USCXML_BENCHMARK_ITERATIONS");
	if (envBenchmarkRuns != NULL) {
		benchmarkRuns = strTo<size_t>(envBenchmarkRuns);
	}

	size_t remainingRuns = benchmarkRuns;

	size_t microSteps = 0;

	StateMachine rootMachine(&USCXML_MACHINE);

	while(remainingRuns-- > 0) {

		microSteps = 0;


		for (;;) {
			err = rootMachine.step();
			if (rootMachine.isDone())
				break;
			microSteps++;
		}
		microSteps++;

		assert(rootMachine.ctx.flags & USCXML_CTX_TOP_LEVEL_FINAL);

		size_t passIdx = 0;
		for (size_t i = 0; i < rootMachine.ctx.machine->nr_states; i++) {
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

	return EXIT_SUCCESS;
}
