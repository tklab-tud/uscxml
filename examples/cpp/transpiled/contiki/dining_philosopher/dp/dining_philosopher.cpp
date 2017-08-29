 #include <string.h>
#include <stdlib.h> // malloc
#include <assert.h> // assert
#include <stdio.h>  // printf
#include <sstream> // stringstream
#include <deque> // deque
#include <boost/algorithm/string.hpp> // trim
#include <iostream>

#include "uscxml/config.h"

#ifdef APPLE
#include <mach/mach.h>
#include <mach/mach_time.h>
#include <pthread.h>
#endif

#include "uscxml/plugins/Factory.h"
#include "uscxml/plugins/IOProcessorImpl.h"
#include "uscxml/plugins/InvokerImpl.h"
#include "uscxml/util/UUID.h"
#include "uscxml/plugins/datamodel/promela/PromelaDataModel.h"
#include "uscxml/interpreter/InterpreterImpl.h"
#include "uscxml/interpreter/BasicEventQueue.h"
#include "uscxml/interpreter/BasicDelayedEventQueue.h"

#ifdef __cplusplus
 #define EXTERNC extern "C"
#else
 #define EXTERNC 
#endif
 
EXTERNC{
#include "contiki.h"
#include "sys/ctimer.h"
}

//including the SCXML transpilation
#include "input/master.c"

//uncomment for verbose run.
//#define USCXML_VERBOSE 
#define USER_DATA(ctx) ((StateMachine*)(((uscxml_ctx*)ctx)->user_data))

//required to circumvent a bug in Contiki Ctimer module.
#ifdef _WIN32
 #define CTIMER_INIT(); 		ctimer_init();
#else 
 #define CTIMER_INIT();	
#endif

//Process declaration
/*---------------------------------------------------------------------------*/
PROCESS(philosopher1_process, "Dining philosopher1 process");
PROCESS(philosopher2_process, "Dining philosopher2 process");
PROCESS(philosopher3_process, "Dining philosopher3 process");
PROCESS(philosopher4_process, "Dining philosopher4 process");
PROCESS(philosopher5_process, "Dining philosopher5 process");
/*---------------------------------------------------------------------------*/
/*---------------------------------------------------------------------------*/
PROCESS(master_process, "Dining philosopher Master process");
AUTOSTART_PROCESSES(&master_process);
/*---------------------------------------------------------------------------*/
using namespace uscxml;

namespace XERCESC_NS {
class DOMDocument;
class DOMNode;
}

class StateMachine : public DataModelCallbacks, public IOProcessorCallbacks, public DelayedEventQueueCallbacks, public InvokerCallbacks {
	public:
	StateMachine(const uscxml_machine* machine) : machine(machine), parentMachine(NULL), topMostMachine(NULL), invocation(NULL) {
		allMachines[sessionId] = this;
		topMostMachine = this;
		currentMachine = this;
		allocate_contiki_event();
		try {
			init();
		} catch (ErrorEvent e) {
			LOGD(USCXML_FATAL) << e;
		}
	}

	StateMachine(StateMachine* parent, const uscxml_machine* machine, const uscxml_elem_invoke* invoke) : machine(machine), invocation(invoke) {
		parentMachine = parent;
		topMostMachine = parent->topMostMachine;
		currentMachine = this;
		init();
	}
	
	ActionLanguage* getActionLanguage() {
		return NULL;
	}

	std::set<InterpreterMonitor*> getMonitors() {
		return std::set<InterpreterMonitor*>();
	}

	std::string getBaseURL() {
		return "";
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

	void enqueueInternal(const Event& event) {
		iq.push_back(event);
	}
	void enqueueExternal(const Event& event) {
		eq.push_back(event);
	}

	void enqueueAtInvoker(const std::string& invokeId, const Event& event) {
		if (invokers.find(invokeId) != invokers.end())
			invokers[invokeId].eventFromSCXML(event);
	}

	void enqueueAtParent(const Event& event) {
		if (parentMachine != NULL)
			parentMachine->enqueueExternal(event);
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
		return NULL;
	}
	const std::map<std::string, Invoker>& getInvokers() {
		return invokers;
	}
	
	void init() {
		sessionId = uscxml::UUID::getUUID();
		isFinalized = false;

		// initialize machine context
		memset(&ctx, 0, sizeof(uscxml_ctx));
		ctx.machine = machine;
		ctx.user_data = (void*)this;

		// register callbacks with SCXML context
		ctx.is_matched = &isMatched;
		ctx.is_true = &isTrue;
		ctx.invoke = &invoke;
		ctx.exec_content_send = &execContentSend;
		ctx.exec_content_cancel = &execContentCancel;
		ctx.exec_content_log = &execContentLog;
		ctx.exec_content_assign = &execContentAssign;
		ctx.dequeue_external = &dequeueExternal;
		ctx.dequeue_internal = &dequeueInternal;
		ctx.raise_done_event = &raiseDoneEvent;
		ctx.exec_content_raise = &execContentRaise;
		ctx.exec_content_init = &execContentInit;

		name = machine->name;
		
		delayQueue = DelayedEventQueue(std::shared_ptr<DelayedEventQueueImpl>(new BasicDelayedEventQueue(this)));
		dataModel = Factory::getInstance()->createDataModel(machine->datamodel, this);
		
		
		if (invocation != NULL) {
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
		
		for (auto Iter = all_timers.begin(); Iter != all_timers.end(); Iter++) {
					ctimer_stop(&(Iter->second.associated_timer));
			}
			
		delayQueue.cancelAllDelayed();
		all_timers.clear();
		
		if (parentMachine != NULL) {
			std::lock_guard<std::mutex> lock(mutex);

			Event done;
			done.invokeid = invokeId;
			done.name = "done.invoke." + invokeId;
			
			std::string target_process = "parent";
			shared_events[done.getUUID()] = done;
			process_post(all_processes[target_process], ce_scxml, &StateMachine::shared_events[done.getUUID()]);
			process_poll(all_processes[target_process]);
			//parentMachine->eq.push_back(done);
		} else {
			shared_events.clear();
			all_processes.clear();
		}
		isFinalized = true;
	}
	
	int step() {

		StateMachine* toRun = currentMachine;
		if (!toRun->hasPendingWork()) {
			return USCXML_ERR_IDLE;
		}

		state = uscxml_step(&toRun->ctx);
		return state;
	}
	
	void eventReady(Event& e, const std::string& eventUUID) {
		std::lock_guard<std::mutex> lock(mutex);

		std::string sendid = std::get<0>(sendUUIDs[e.getUUID()]);
		std::string target = std::get<1>(sendUUIDs[e.getUUID()]);
		std::string type = std::get<2>(sendUUIDs[e.getUUID()]);
		
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
			
			if(type=="contiki"){
				std::string target_process = target.substr(2,target.size()-2);
				shared_events[e.getUUID()] = e;
				
				process_post(all_processes[target_process], ce_scxml, &StateMachine::shared_events[e.getUUID()]);
				process_poll(all_processes[target_process]);
			} else{
				if (parentMachine != NULL) {
					parentMachine->eq.push_back(e);
				}
			}
		} else if (target.substr(0,8) == "#_scxml_") {
			std::string sessionId = target.substr(8);
			bool sessionFound = false;
			
			for (std::map<std::string, StateMachine*>::iterator machIter = topMostMachine->allMachines.begin();
			        machIter != topMostMachine->allMachines.end(); machIter++) {
				if (machIter->second->sessionId == sessionId) {
					e.eventType = Event::EXTERNAL;
					//handle send type "contiki"
					if(type=="contiki"){
						shared_events[e.getUUID()] = e;
						process_post(machIter->second->contiki_process, ce_scxml, &StateMachine::shared_events[e.getUUID()]);
						process_poll(machIter->second->contiki_process);
					}else{
						machIter->second->eq.push_back(e);
					}
					sessionFound = true;
					break;
				}
			}
			if (!sessionFound) {
				execContentRaise(&ctx, "error.communication");
			}
		} else if (target.substr(0,2) == "#_") {
			e.eventType = Event::EXTERNAL;
			std::string targetId = target.substr(2);

			if(type=="contiki"){
				std::string target_process = targetId;
				shared_events[e.getUUID()] = e;
				
				process_post(all_processes[target_process], ce_scxml, &StateMachine::shared_events[e.getUUID()]);
				process_poll(all_processes[target_process]);
			}else{
				
				if (topMostMachine->allMachines.find(targetId) != topMostMachine->allMachines.end()) {
					topMostMachine->allMachines[targetId]->eq.push_back(e);
				} else {
					execContentRaise(&ctx, "error.communication");
				}
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
	
	// callbacks for scxml context
	
	static int execContentScript(const uscxml_ctx* ctx, const char* src, const char* content) {
		if (content != NULL) {
			USER_DATA(ctx)->dataModel.evalAsData(content);
		} else if (src != NULL) {
			return USCXML_ERR_UNSUPPORTED;
		}
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
				//content.
				try {
					if (data->expr != NULL) {
						d = Data(data->expr, Data::INTERPRETED);
//						d = USER_DATA(ctx)->dataModel.evalAsData(data->expr);

					} else if (data->content != NULL || data->src != NULL) {
						if (data->content) {
							content << data->content;
						} else {
// avoid dependency on URL.cpp -> urlparser -> curl
#if 0
							URL sourceURL(data->src);
							if (USER_DATA(ctx)->baseURL.size() > 0) {
								sourceURL = URL::resolve(sourceURL, USER_DATA(ctx)->baseURL);
							} else {
								sourceURL = URL::resolveWithCWD(sourceURL);
							}
							content << sourceURL.getInContent();
#endif
						}
						/**
						 * first attempt to parse as structured data, we will try
						 * as space normalized string literals if this fails below
						 */
						d = USER_DATA(ctx)->dataModel.getAsData(content.str());
						if (d.empty()) {
							d = Data(escape(spaceNormalize(content.str())), Data::VERBATIM);
						}
					} else {
						// leave d undefined
					}
					
					std::map<std::string, std::string> attr;
					if (d.array.size() > 0) {
						
						attr["id"] = data->id;
						std::stringstream content;
						content <<  "int["<< d.array.size()<<"]";
						attr["type"] = content.str();
					}
					// this might fail with an unquoted string literal in content
					USER_DATA(ctx)->dataModel.init(data->id, d, attr);

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
		printf("Popping External Event: %s with origin : %s\n", e.name.c_str(),e.origin.c_str());
#endif
		return &USER_DATA(ctx)->currEvent;
	}
	
	static int invoke(const uscxml_ctx* ctx, const uscxml_state* s, const uscxml_elem_invoke* invocation, unsigned char uninvoke) {
		//printf("in invoke for invocation id: %s with ctx->machine.name : %s\n",invocation->id, ctx->machine->name);
		std::map<std::string, StateMachine*> &allMachines = USER_DATA(ctx)->topMostMachine->allMachines;
		StateMachine* topMachine = USER_DATA(ctx)->topMostMachine;
		
		if (uninvoke){
			if (invocation->machine != NULL) {
				for (std::map<std::string, StateMachine*>::iterator iter = USER_DATA(ctx)->topMostMachine->allMachines.begin(); iter != USER_DATA(ctx)->topMostMachine->allMachines.end(); iter++)
			{
				
				if (!(iter->second->invokeId.empty()))
				{					
					iter->second->finalize();
				}
			}
				
				if (topMachine->invocationIds.find(invocation) != topMachine->invocationIds.end() &&
				        allMachines.find(topMachine->invocationIds[invocation]) != allMachines.end()) {

					delete allMachines[topMachine->invocationIds[invocation]];
					topMachine->allMachines.erase(topMachine->invocationIds[invocation]);
					topMachine->invocationIds.erase(invocation);
					printf("uninvoke called. exiting process: %s. \n", invocation->id);
					if(invocation->id!=NULL){
						std::string target_process = invocation->id;
						if(process_is_running(all_processes[target_process]))
							process_exit(all_processes[target_process]);
					}
				}
			}
		} else{
			// invoke a nested SCXML machine
			StateMachine* invokedMachine = NULL;
			std::string target_process ;
			try {
				invokedMachine = new StateMachine(USER_DATA(ctx), invocation->machine, invocation);
			} catch (Event e) {
				delete invokedMachine;
				return USCXML_ERR_EXEC_CONTENT;
			}
			if(invocation->id!=NULL){
				target_process = invocation->id;
				invokedMachine->invokeId = invocation->id;
			} else{
				printf("for contiki scaffolding invoke id is must and should be equal to invoke process name.");
				assert(false);
			}
			
			allMachines[invokedMachine->invokeId] = invokedMachine;
			topMachine->invocationIds[invocation] = invokedMachine->invokeId;
			process_start(all_processes[target_process],invokedMachine);
		}
		
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
			std::cerr << "Target '" << target << "' is not supported yet" << std::endl;
			e.name = "error.execution";
			execContentRaise(ctx, e);
			return USCXML_ERR_INVALID_TARGET;
		}

		e.origintype = "http://www.w3.org/TR/scxml/#SCXMLEventProcessor";

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

		
		if (type == "http://www.w3.org/TR/scxml/#SCXMLEventProcessor" || type == "contiki"){
		} 
		else{
			e.name = "error.execution";
			execContentRaise(ctx, e);
			return USCXML_ERR_INVALID_TARGET;
		}

		e.origintype = type;
		e.origin = "#_scxml_" + USER_DATA(ctx)->sessionId;
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
			try {
				Data d = USER_DATA(ctx)->dataModel.getAsData(send->content);
				if (!d.empty()) {
					e.data = d;
				}
			} catch (Event err) {
				e.data = Data(spaceNormalize(send->content), Data::VERBATIM);
			}
		}

		size_t delayMs = 0;
		if (send->delayexpr != NULL) {
			std::string delay = USER_DATA(ctx)->dataModel.evalAsData(send->delayexpr).atom;
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
		} else if (send->delay > 0) {
			delayMs = (size_t)(send->delay);
		}

		if (USER_DATA(ctx)->invokeId.size() > 0) {
			e.invokeid = USER_DATA(ctx)->invokeId;
		}

		sendUUIDs[e.getUUID()] = std::make_tuple(e.sendid, target, type);
		
		if (delayMs > 0) {
			// delay event with send type contiki use Contiki Ctimer library
			if(type == "contiki"){
				int delayS = delayMs/1000;
				struct timer_event_contiki t_e ;
				struct ctimer ct;
				t_e.associated_timer = ct;
				t_e.associated_ctx_event.context = ctx;
				t_e.associated_ctx_event.event = e;
			
				USER_DATA(ctx)->all_timers[e.getUUID()] = t_e;
	
				ctimer_set(&(USER_DATA(ctx)->all_timers[e.getUUID()].associated_timer), CLOCK_SECOND*delayS, &ctimer_callback, &(USER_DATA(ctx)->all_timers[e.getUUID()].associated_ctx_event));
			} else{
			USER_DATA(ctx)->delayQueue.enqueueDelayed(e, delayMs, e.getUUID());
			}
		} else {
			
				USER_DATA(ctx)->eventReady(e, e.getUUID());		
		}		
		return USCXML_ERR_OK;
	}
	
	
	static void ctimer_callback(void* data){
		struct context_event event_enqueue = *((struct context_event*)data);
		const uscxml_ctx* ctx = event_enqueue.context;
		USER_DATA(ctx)->all_timers.erase(event_enqueue.event.getUUID());
		USER_DATA(ctx)->eventReady(event_enqueue.event, event_enqueue.event.getUUID());
		process_poll(USER_DATA(ctx)->contiki_process);
	}
	
	static int raiseDoneEvent(const uscxml_ctx* ctx, const uscxml_state* state, const uscxml_elem_donedata* donedata) {
		Event e;
		e.name = std::string("done.state.") + state->name;

#ifdef USCXML_VERBOSE
		printf("Raising Done Event: %s\n", e.name.c_str());
#endif
		USER_DATA(ctx)->iq.push_back(e);
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
						
			for (auto evIter = sendUUIDs.begin(); evIter != sendUUIDs.end(); evIter++) {
				std::string sendid = std::get<0>(evIter->second);
				if (eventId == sendid) {
					auto search = USER_DATA(ctx)->all_timers.find(evIter->first);
					if(search != USER_DATA(ctx)->all_timers.end()) {
						ctimer_stop(&(search->second.associated_timer));
						USER_DATA(ctx)->all_timers.erase(search->first);
					}else{
						USER_DATA(ctx)->delayQueue.cancelDelayed(evIter->first);
					}
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
			if (assign->expr != NULL) {
				USER_DATA(ctx)->dataModel.assign(key, Data(assign->expr, Data::INTERPRETED));
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
	
	/* allocate the required event */
	static void allocate_contiki_event(){
		ce_scxml = process_alloc_event();
		ce_timer = process_alloc_event();
	}
	
	static void register_philosophers(){
		std::string parent = "parent";
		all_processes[parent] = &master_process;
		
		std::string phil_id = "philosopher1";
		all_processes[phil_id] = &philosopher1_process;
		
		phil_id = "philosopher2";
		all_processes[phil_id] = &philosopher2_process;
		
		phil_id = "philosopher3";
		all_processes[phil_id] = &philosopher3_process;
		
		phil_id = "philosopher4";
		all_processes[phil_id] = &philosopher4_process;
		
		phil_id = "philosopher5";
		all_processes[phil_id] = &philosopher5_process;
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
	StateMachine* currentMachine;

	std::string baseURL;
	std::string sessionId;
	std::string name;

	// in case we were invoked
	std::string invokeId;
	const uscxml_elem_invoke* invocation;
	std::map<std::string, Data> invokeData;

	std::map<const uscxml_elem_invoke*, Invoker> _invocations;

	std::deque<Event> iq;
	std::deque<Event> eq;

	DataModel dataModel;
	std::map<std::string, IOProcessor> ioProcs;
	std::map<std::string, Invoker> invokers;
	
	struct context_event{
		const uscxml_ctx* context;
		Event event;
	};
	
	struct timer_event_contiki{
		struct ctimer associated_timer;
		struct context_event associated_ctx_event;
	};
	
	struct process* contiki_process;
	std::map<std::string, struct timer_event_contiki> all_timers;
	static std::map<const std::string, struct process*> all_processes; //
	static std::map<std::string, Event> shared_events;
	
	Event event_to_enque;
	
	static process_event_t ce_scxml;
	static process_event_t ce_timer;

protected:

	DelayedEventQueue delayQueue;
	static std::map<std::string, std::tuple<std::string, std::string, std::string> > sendUUIDs;

	std::condition_variable monitor;
	std::mutex mutex;
};

std::map<const std::string, struct process*> StateMachine::all_processes;
std::map<std::string, Event> StateMachine::shared_events;
std::map<std::string, std::tuple<std::string, std::string, std::string> > StateMachine::sendUUIDs;
	
process_event_t StateMachine::ce_scxml;
process_event_t StateMachine::ce_timer;

	
PROCESS_THREAD(master_process, ev, data)
{  
	static StateMachine rootMachine(&USCXML_MACHINE);
	static int err = 0;
	static int process_called_before =0;
	
	if(!process_called_before){
		CTIMER_INIT();
		StateMachine::register_philosophers();
		rootMachine.contiki_process = PROCESS_CURRENT();
		Factory::getInstance()->registerDataModel(new PromelaDataModel());
		process_called_before++;
	}

  PROCESS_BEGIN();
	for (;;) {
		
		while ( err != USCXML_ERR_IDLE && err != USCXML_ERR_DONE) { 
			err = rootMachine.step();
		}
			
		if(err == USCXML_ERR_DONE){
			rootMachine.finalize();
			break;
		} else if(err == USCXML_ERR_IDLE){
				
			PROCESS_YIELD_UNTIL(rootMachine.hasPendingWork() || ev == StateMachine::ce_scxml);
			
				if(ev == StateMachine::ce_scxml){
					
					Event* rcvd_event = (Event*)data;
					rootMachine.event_to_enque = *rcvd_event;
					
					StateMachine::shared_events.erase(rootMachine.event_to_enque.getUUID());
					printf("Master :  event received: %s \n", rootMachine.event_to_enque.name.c_str());
				
					rootMachine.eq.push_back(rootMachine.event_to_enque);				
				} else if(ev == StateMachine::ce_timer){
					printf("event received ce_timer.\n");
					}
				ev=PROCESS_EVENT_CONTINUE;
			} else{continue;}
		err=0;
	}
  PROCESS_END();
}

PROCESS_THREAD(philosopher1_process, ev, data)
{  
	static int process_called_before =0;
	static StateMachine* ptr_invoked_machine = NULL;
	
	if(!process_called_before){
		if(data != NULL){
			ptr_invoked_machine = (StateMachine*)data;
			ptr_invoked_machine->contiki_process = PROCESS_CURRENT();
		}
		process_called_before++;
	}
	static int err;
  PROCESS_BEGIN();
	for (;;) {
		
		while ( err != USCXML_ERR_IDLE && err != USCXML_ERR_DONE) { 
			err = ptr_invoked_machine->step();
		}
			
		if(err == USCXML_ERR_DONE){
			ptr_invoked_machine->finalize();
			break;
		} else if(err == USCXML_ERR_IDLE){
				
			PROCESS_YIELD_UNTIL(ptr_invoked_machine->hasPendingWork() || ev == StateMachine::ce_scxml);
			
				if(ev == StateMachine::ce_scxml){
					
					Event* rcvd_event = (Event*)data;
					ptr_invoked_machine->event_to_enque = *rcvd_event;
					
					StateMachine::shared_events.erase(ptr_invoked_machine->event_to_enque.getUUID());
					printf("philosopher1 :  event received: %s \n", ptr_invoked_machine->event_to_enque.name.c_str());
				
					ptr_invoked_machine->eq.push_back(ptr_invoked_machine->event_to_enque);				
				} else if(ev == StateMachine::ce_timer){
					printf("event received ce_timer.\n");
					}
					ev=PROCESS_EVENT_CONTINUE;
			} else{continue;}
		err=0;
	}
  PROCESS_END();
}

PROCESS_THREAD(philosopher2_process, ev, data)
{  
	static int process_called_before =0;
	static StateMachine* ptr_invoked_machine = NULL;
	
	if(!process_called_before){
		if(data != NULL){
			ptr_invoked_machine = (StateMachine*)data;
			ptr_invoked_machine->contiki_process = PROCESS_CURRENT();
		}
		process_called_before++;
	}
	static int err;
	PROCESS_BEGIN();
	for (;;) {
		
		if(ptr_invoked_machine->isFinalized){
				PROCESS_EXIT();
			}
			
		while ( err != USCXML_ERR_IDLE && !ptr_invoked_machine->isFinalized) { 
			
			err = ptr_invoked_machine->step();
		}
		
		if(err == USCXML_ERR_DONE){
			ptr_invoked_machine->finalize();
			break;
		} else if(err == USCXML_ERR_IDLE){
							
			PROCESS_YIELD_UNTIL(ptr_invoked_machine->hasPendingWork() || ev == StateMachine::ce_scxml);
		
				if(ev == StateMachine::ce_scxml){
					
					Event* rcvd_event = (Event*)data;
					ptr_invoked_machine->event_to_enque = *rcvd_event;
					
					StateMachine::shared_events.erase(ptr_invoked_machine->event_to_enque.getUUID());
					printf("philosopher2 :  event received: %s \n", ptr_invoked_machine->event_to_enque.name.c_str());
				
					ptr_invoked_machine->eq.push_back(ptr_invoked_machine->event_to_enque);				
				} else if(ev == StateMachine::ce_timer){
					printf("event received ce_timer.\n");
					}
					ev=PROCESS_EVENT_CONTINUE;
			} else{continue;}
		err=0;
	}
  PROCESS_END();
}

PROCESS_THREAD(philosopher3_process, ev, data)
{  
	static int process_called_before =0;
	static StateMachine* ptr_invoked_machine = NULL;
	
	if(!process_called_before){
		if(data != NULL){
			ptr_invoked_machine = (StateMachine*)data;
			ptr_invoked_machine->contiki_process = PROCESS_CURRENT();
		}
		process_called_before++;
	}
	static int err;
	PROCESS_BEGIN();
	for (;;) {
		
		if(ptr_invoked_machine->isFinalized){
				PROCESS_EXIT();
			}
			
		while ( err != USCXML_ERR_IDLE && err != USCXML_ERR_DONE) { 
			err = ptr_invoked_machine->step();
		}
			
		if(err == USCXML_ERR_DONE){
			ptr_invoked_machine->finalize();
			break;
		} else if(err == USCXML_ERR_IDLE){
						
			PROCESS_YIELD_UNTIL(ptr_invoked_machine->hasPendingWork() || ev == StateMachine::ce_scxml);
			
				if(ev == StateMachine::ce_scxml){
					
					Event* rcvd_event = (Event*)data;
					ptr_invoked_machine->event_to_enque = *rcvd_event;
					
					StateMachine::shared_events.erase(ptr_invoked_machine->event_to_enque.getUUID());
					printf("philosopher3 :  event received: %s \n", ptr_invoked_machine->event_to_enque.name.c_str());
				
					ptr_invoked_machine->eq.push_back(ptr_invoked_machine->event_to_enque);				
				} else if(ev == StateMachine::ce_timer){
					printf("event received ce_timer.\n");
					}
					ev=PROCESS_EVENT_CONTINUE;
			} else{continue;}
		err=0;
	}
  PROCESS_END();
}

PROCESS_THREAD(philosopher4_process, ev, data)
{  
	static int process_called_before =0;
	static StateMachine* ptr_invoked_machine = NULL;
	
	if(!process_called_before){
		if(data != NULL){
			ptr_invoked_machine = (StateMachine*)data;
			ptr_invoked_machine->contiki_process = PROCESS_CURRENT();
		}
		process_called_before++;
	}
	static int err;
	PROCESS_BEGIN();
	for (;;) {
		
		if(ptr_invoked_machine->isFinalized){
				PROCESS_EXIT();
			}
			
		while ( err != USCXML_ERR_IDLE && err != USCXML_ERR_DONE) { 
			err = ptr_invoked_machine->step();
		}
			
		if(err == USCXML_ERR_DONE){
			ptr_invoked_machine->finalize();
			break;
		} else if(err == USCXML_ERR_IDLE){
					
			PROCESS_YIELD_UNTIL(ptr_invoked_machine->hasPendingWork() || ev == StateMachine::ce_scxml);
			
				if(ev == StateMachine::ce_scxml){
					
					Event* rcvd_event = (Event*)data;
					ptr_invoked_machine->event_to_enque = *rcvd_event;
					
					StateMachine::shared_events.erase(ptr_invoked_machine->event_to_enque.getUUID());
					printf("philosopher4 :  event received: %s \n", ptr_invoked_machine->event_to_enque.name.c_str());
				
					ptr_invoked_machine->eq.push_back(ptr_invoked_machine->event_to_enque);				
				} else if(ev == StateMachine::ce_timer){
					printf("event received ce_timer.\n");
					}
					ev=PROCESS_EVENT_CONTINUE;
			} else{continue;}
		err=0;
	}
  PROCESS_END();
}

PROCESS_THREAD(philosopher5_process, ev, data)
{  
	static int process_called_before =0;
	static StateMachine* ptr_invoked_machine = NULL;
	
	if(!process_called_before){
		if(data != NULL){
			ptr_invoked_machine = (StateMachine*)data;
			ptr_invoked_machine->contiki_process = PROCESS_CURRENT();
		}
		process_called_before++;
	}
	static int err;
	PROCESS_BEGIN();
	for (;;) {
		
		if(ptr_invoked_machine->isFinalized){
				PROCESS_EXIT();
			}
		
		while ( err != USCXML_ERR_IDLE && err != USCXML_ERR_DONE) { 
			err = ptr_invoked_machine->step();
			
		}
			
		if(err == USCXML_ERR_DONE){
			ptr_invoked_machine->finalize();
			break;
		} else if(err == USCXML_ERR_IDLE){
						
			PROCESS_YIELD_UNTIL(ptr_invoked_machine->hasPendingWork() || ev == StateMachine::ce_scxml);
			
				if(ev == StateMachine::ce_scxml){
					
					Event* rcvd_event = (Event*)data;
					ptr_invoked_machine->event_to_enque = *rcvd_event;
					
					StateMachine::shared_events.erase(ptr_invoked_machine->event_to_enque.getUUID());
					printf("philosopher5 :  event received: %s \n", ptr_invoked_machine->event_to_enque.name.c_str());
				
					ptr_invoked_machine->eq.push_back(ptr_invoked_machine->event_to_enque);				
				} else if(ev == StateMachine::ce_timer){
					printf("event received ce_timer.\n");
					}
					ev=PROCESS_EVENT_CONTINUE;
			} else{continue;}
		err=0;
	}
  PROCESS_END();
}