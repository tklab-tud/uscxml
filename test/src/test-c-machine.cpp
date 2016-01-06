#include <string.h>
#include <stdlib.h> // malloc
#include <assert.h> // assert
#include <stdio.h>  // printf
#include <sstream> // stringstream
#include <deque> // deque
#include <boost/algorithm/string.hpp> // trim

#define SCXML_VERBOSE 1

#ifndef AUTOINCLUDE_TEST
#include "test-c-machine.machine.c"
#endif

#include "uscxml/Convenience.h"
//#include "uscxml/DOMUtils.h"
#include "uscxml/Factory.h"
#include "uscxml/InterpreterInfo.h"
#include "uscxml/UUID.h"

#include "uscxml/concurrency/DelayedEventQueue.h"
#include "uscxml/concurrency/tinythread.h"

#define USER_DATA(ctx) ((GenCInterpreterInfo*)(((scxml_ctx*)ctx)->user_data))

using namespace uscxml;

typedef struct scxml_foreach_info scxml_foreach_info;
struct scxml_foreach_info {
    size_t iterations;
    size_t currIteration;
};

class GenCInterpreterInfo : public InterpreterInfo {
public:
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
    bool isInState(const std::string& stateId) {
        for (int i = 0 ; i < SCXML_NUMBER_STATES; i++) {
            if (scxml_states[i].name != NULL && IS_SET(i, ctx->config) && stateId == scxml_states[i].name)
                return true;
        }
        return false;
    }
    Arabica::DOM::Document<std::string> getDocument() const {
        return document;
    }
    const std::map<std::string, Invoker>& getInvokers() {
        return invokers;
    }
    
    NameSpaceInfo nsInfo;
    std::string name;
    std::string sessionId;
    std::map<std::string, IOProcessor> ioProcs;
    std::map<std::string, Invoker> invokers;
    Arabica::DOM::Document<std::string> document;
    scxml_ctx* ctx;
    boost::shared_ptr<DataModelImpl> datamodel;
    
    std::map<const scxml_elem_foreach*, scxml_foreach_info*> foreachInfo;
    std::deque<Event*> iq;
    std::deque<Event*> eq;
    
    DelayedEventQueue delayQueue;
    std::map<std::string, SendRequest*> sendIds;

    tthread::condition_variable monitor;
    tthread::mutex mutex;
};

int matches(const char* desc, const char* event) {
    const char* dPtr = desc;
    const char* ePtr = event;
    while(true) {

        // next event descriptor
        if (*dPtr == ' ') {
            dPtr++;
            ePtr = event;
            continue;
        }
        
        // descriptor is done, return match
        if (*dPtr == 0 || *dPtr == '*')
            return true;
        
        // descriptor differs from event name
        if (*dPtr != *ePtr)
            return false;

        // move both pointers one character
        dPtr++;
        ePtr++;
    }
}

int exec_content_raise(const scxml_ctx* ctx, const char* event) {
    Event* e = new Event();
    e->name = strdup(event);
    printf("Raising Internal Event: %s\n", e->name.c_str());
    USER_DATA(ctx)->iq.push_back(e);
    return SCXML_ERR_OK;
}

int is_true(const scxml_ctx* ctx, const char* expr) {
    try {
        return USER_DATA(ctx)->datamodel->evalAsBool(expr);
    } catch (Event e) {
        exec_content_raise(ctx, e.name.c_str());
    }
    return false;
}

int is_enabled(const scxml_ctx* ctx, const scxml_transition* t, const void* e) {
    Event* event = (Event*)e;
    if (event == NULL) {
        if (t->event == NULL) {
            // spontaneous transition, null event
            if (t->condition != NULL)
                return is_true(ctx, t->condition);
            return true;
        } else {
            // spontaneous transition, but real event
            return false;
        }
    }

    // real transition, real event
    if (matches(t->event, event->name.c_str())) {
        if (t->condition != NULL)
            return is_true(ctx, t->condition);
        return true;
    }
    return false;
}

int raise_done_event(const scxml_ctx* ctx, const scxml_state* state) {
    std::string doneName = "done.state.";
    exec_content_raise(ctx, (doneName + state->name).c_str());
    return SCXML_ERR_OK;
}

void delayedSend(void* ctx, std::string eventName) {
    tthread::lock_guard<tthread::mutex> lock(USER_DATA(ctx)->mutex);

    SendRequest* e = USER_DATA(ctx)->sendIds[eventName];
    if (e->target == "#_internal") {
        printf("Pushing Internal Event: %s\n", e->name.c_str());
        USER_DATA(ctx)->iq.push_back(e);
    } else {
        printf("Pushing External Event: %s\n", e->name.c_str());
        USER_DATA(ctx)->eq.push_back(e);
    }
    USER_DATA(ctx)->monitor.notify_all();
}

int exec_content_cancel(const scxml_ctx* ctx, const char* sendid, const char* sendidexpr) {
    std::string eventId;
    if (sendid != NULL) {
        eventId = sendid;
    } else if (sendidexpr != NULL) {
        eventId = USER_DATA(ctx)->datamodel->evalAsString(sendidexpr);
    }
    
    if (eventId.length() > 0) {
        USER_DATA(ctx)->delayQueue.cancelEvent(eventId);
    } else {
        exec_content_raise(ctx, "error.execution");
        return SCXML_ERR_EXEC_CONTENT;
    }
    return SCXML_ERR_OK;
}

int exec_content_send(const scxml_ctx* ctx, const scxml_elem_send* send) {
    SendRequest* e = new SendRequest();
    
    std::string target;
    if (send->target != NULL) {
        e->target = send->target;
    } else if (send->targetexpr != NULL) {
        e->target = USER_DATA(ctx)->datamodel->evalAsString(send->targetexpr);
    }
    
    if (e->target.size() > 0 && (e->target[0] != '#' || e->target[1] != '_')) {
        delete e;
        exec_content_raise(ctx, "error.execution");
        return SCXML_ERR_INVALID_TARGET;
    }
    
    if (send->type != NULL) {
        e->type = send->type;
    } else if (send->typeexpr != NULL) {
        e->type = USER_DATA(ctx)->datamodel->evalAsString(send->typeexpr);
    } else {
        e->type = "http://www.w3.org/TR/scxml/#SCXMLEventProcessor";
    }
    
    // only one somewhat supported
    if (e->type != "http://www.w3.org/TR/scxml/#SCXMLEventProcessor") {
        delete e;
        exec_content_raise(ctx, "error.execution");
        return SCXML_ERR_INVALID_TARGET;
    }
    
    e->origintype = e->type;
    
    if (send->eventexpr != NULL) {
        e->name = USER_DATA(ctx)->datamodel->evalAsString(send->eventexpr);
    } else {
        e->name = strdup(send->event);
    }
    
    const scxml_elem_param* param = send->params;
    while (param && ELEM_PARAM_IS_SET(param)) {
        Data paramValue;
        if (param->expr != NULL) {
            paramValue = USER_DATA(ctx)->datamodel->getStringAsData(param->expr);
        } else if(param->location) {
            paramValue = USER_DATA(ctx)->datamodel->getStringAsData(param->location);
        }
        e->params.insert(std::make_pair(param->name, paramValue));
        param++;
    }
    
    if (send->content != NULL) {
        e->data = Data(send->content, Data::VERBATIM);
    }
    
    const char* sendid = NULL;
    if (send->id != NULL) {
        sendid = send->id;
    } else {
        sendid = strdup(UUID::getUUID().c_str());
        if (send->idlocation != NULL)
            USER_DATA(ctx)->datamodel->assign(send->idlocation, Data(sendid, Data::VERBATIM));
    }
    
    size_t delayMs = 0;
    std::string delay;
    if (send->delayexpr != NULL) {
        delay = USER_DATA(ctx)->datamodel->evalAsString(send->delayexpr);
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
    
    USER_DATA(ctx)->sendIds[sendid] = e;
    if (delayMs > 0) {
        USER_DATA(ctx)->delayQueue.addEvent(sendid, delayedSend, delayMs, (void*)ctx);
    } else {
        delayedSend((void*)ctx, sendid);
    }
    
    return SCXML_ERR_OK;
}

int exec_content_init(const scxml_ctx* ctx, const scxml_elem_data* data) {
    while(ELEM_DATA_IS_SET(data)) {
        Data d;
        if (data->expr != NULL) {
            d = Data(data->expr, Data::INTERPRETED);
        } else if (data->content != NULL) {
            d = Data(data->content, Data::INTERPRETED);
        } else {
            d = Data("undefined", Data::INTERPRETED);
        }
        try {
            USER_DATA(ctx)->datamodel->init(data->id, d);
        } catch (Event e) {
            exec_content_raise(ctx, e.name.c_str());
        }
        data++;
    }
    return SCXML_ERR_OK;
}

int exec_content_assign(const scxml_ctx* ctx, const char* location, const char* expr) {
    try {
        Data d(expr, Data::INTERPRETED);
        USER_DATA(ctx)->datamodel->assign(location, d);
    } catch (Event e) {
        exec_content_raise(ctx, e.name.c_str());
        return SCXML_ERR_EXEC_CONTENT;
    }
    return SCXML_ERR_OK;
}

int exec_content_foreach_init(const scxml_ctx* ctx, const scxml_elem_foreach* foreach) {
    try {
        scxml_foreach_info* feInfo = (scxml_foreach_info*)malloc(sizeof(scxml_foreach_info));
        USER_DATA(ctx)->foreachInfo[foreach] = feInfo;
        
        feInfo->iterations = USER_DATA(ctx)->datamodel->getLength(foreach->array);
        feInfo->currIteration = 0;
    } catch (Event e) {
        exec_content_raise(ctx, e.name.c_str());
        return SCXML_ERR_EXEC_CONTENT;
    }
    return SCXML_ERR_OK;
}

int exec_content_foreach_next(const scxml_ctx* ctx, const scxml_elem_foreach* foreach) {
    try {
        scxml_foreach_info* feInfo = USER_DATA(ctx)->foreachInfo[foreach];
        if (feInfo->currIteration < feInfo->iterations) {
            USER_DATA(ctx)->datamodel->setForeach((foreach->item != NULL ? foreach->item : ""),
                                                  (foreach->array != NULL ? foreach->array : ""),
                                                  (foreach->index != NULL ? foreach->index : ""),
                                                  feInfo->currIteration);
            feInfo->currIteration++;
            return SCXML_ERR_OK;
        }
    } catch (Event e) {
        exec_content_raise(ctx, e.name.c_str());
        free(USER_DATA(ctx)->foreachInfo[foreach]);
        USER_DATA(ctx)->foreachInfo.erase(foreach);
        return SCXML_ERR_EXEC_CONTENT;
    }
    return SCXML_ERR_FOREACH_DONE;
}

int exec_content_foreach_done(const scxml_ctx* ctx, const scxml_elem_foreach* foreach) {
    free(USER_DATA(ctx)->foreachInfo[foreach]);
    USER_DATA(ctx)->foreachInfo.erase(foreach);
    return SCXML_ERR_OK;
}

int exec_content_log(const scxml_ctx* ctx, const char* label, const char* expr) {
    if (label != 0) {
        printf("%s: %s\n", label, expr);
    } else {
        printf("%s\n", USER_DATA(ctx)->datamodel->evalAsString(expr).c_str());
    }
    return SCXML_ERR_OK;
}

void* dequeue_external(const scxml_ctx* ctx) {
    tthread::lock_guard<tthread::mutex> lock(USER_DATA(ctx)->mutex);
    while (USER_DATA(ctx)->eq.size() == 0) {
        USER_DATA(ctx)->monitor.wait(USER_DATA(ctx)->mutex);
    }
    Event* e = USER_DATA(ctx)->eq.front();
    USER_DATA(ctx)->eq.pop_front();
    USER_DATA(ctx)->datamodel->setEvent(*e);
    printf("Popping External Event: %s\n", e->name.c_str());
    return e;
}

void* dequeue_internal(const scxml_ctx* ctx) {
    if (USER_DATA(ctx)->iq.size() == 0)
        return NULL;
    Event* e = USER_DATA(ctx)->iq.front();
    USER_DATA(ctx)->iq.pop_front();
    USER_DATA(ctx)->datamodel->setEvent(*e);
    printf("Popping Internal Event: %s\n", e->name.c_str());
    return e;
}

int main(int argc, char** argv) {
    int err;
    
    // setup info object required for datamodel
    GenCInterpreterInfo interpreterInfo;
    interpreterInfo.name = "adsf";
    interpreterInfo.sessionId = "rfwef";
    interpreterInfo.datamodel = Factory::getInstance()->createDataModel("ecmascript", &interpreterInfo);
    interpreterInfo.delayQueue.start();
    
    scxml_ctx ctx;
    memset(&ctx, 0, sizeof(scxml_ctx));
    interpreterInfo.ctx = &ctx;
    
    // set info object as user data
    ctx.user_data = (void*)&interpreterInfo;
    
    // register callbacks with scxml context
    ctx.is_enabled = &is_enabled;
    ctx.is_true = &is_true;
    ctx.raise_done_event = &raise_done_event;
    
    ctx.exec_content_send = &exec_content_send;
    ctx.exec_content_raise = &exec_content_raise;
    ctx.exec_content_cancel = &exec_content_cancel;
    ctx.exec_content_log = &exec_content_log;
    ctx.exec_content_assign = &exec_content_assign;
    ctx.exec_content_foreach_init = &exec_content_foreach_init;
    ctx.exec_content_foreach_next = &exec_content_foreach_next;
    ctx.exec_content_foreach_done = &exec_content_foreach_done;
    ctx.dequeue_external = &dequeue_external;
    ctx.dequeue_internal = &dequeue_internal;
    ctx.exec_content_init = &exec_content_init;
    
    while((err = scxml_step(&ctx)) == SCXML_ERR_OK);
    assert(ctx.flags & SCXML_CTX_TOP_LEVEL_FINAL);
    
    size_t passIdx = 0;
    for (int i = 0; i < SCXML_NUMBER_STATES; i++) {
        if (scxml_states[i].name && strcmp(scxml_states[i].name, "pass") == 0) {
            passIdx = i;
            break;
        }
    }
    assert(IS_SET(passIdx, ctx.config));
    return EXIT_SUCCESS;
}