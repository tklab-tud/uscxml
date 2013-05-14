#include "MMIProtoBridge.h"

#define INIT_PROTO_LIFE_CYCLE_EVENT(type) \
::LifeCycleEvent lifeCycleEvent; \
lifeCycleEvent.set_type(type); \
lifeCycleEvent.set_requestid(mmiEvent.requestId); \
lifeCycleEvent.set_source(mmiEvent.source); \
lifeCycleEvent.set_target(mmiEvent.target);

namespace uscxml {

::LifeCycleEvent MMIProtoBridge::toProto(const NewContextRequest& mmiEvent) {
	INIT_PROTO_LIFE_CYCLE_EVENT(::LifeCycleEvent_LifeCycleEventType_NEW_CONTEXT_REQUEST);
	return lifeCycleEvent;	
}

::LifeCycleEvent MMIProtoBridge::toProto(const NewContextResponse& mmiEvent) {
	INIT_PROTO_LIFE_CYCLE_EVENT(::LifeCycleEvent_LifeCycleEventType_NEW_CONTEXT_RESPONSE);
	return lifeCycleEvent;
}

::LifeCycleEvent MMIProtoBridge::toProto(const PrepareRequest& mmiEvent) {
	INIT_PROTO_LIFE_CYCLE_EVENT(::LifeCycleEvent_LifeCycleEventType_PREPARE_REQUEST);
	return lifeCycleEvent;
}

::LifeCycleEvent MMIProtoBridge::toProto(const PrepareResponse& mmiEvent) {
	INIT_PROTO_LIFE_CYCLE_EVENT(::LifeCycleEvent_LifeCycleEventType_PREPARE_RESPONSE);
	return lifeCycleEvent;
}

::LifeCycleEvent MMIProtoBridge::toProto(const StartRequest& mmiEvent) {
	INIT_PROTO_LIFE_CYCLE_EVENT(::LifeCycleEvent_LifeCycleEventType_START_REQUEST);

	::LifeCycleRequest* lifeCycleRequest = lifeCycleEvent.MutableExtension(::LifeCycleRequest::Request);	
	lifeCycleRequest->set_context(mmiEvent.context);
	
	::StartRequest* startRequest = lifeCycleRequest->MutableExtension(::StartRequest::Request);
	startRequest->set_content(mmiEvent.content);
	startRequest->set_contenturl(mmiEvent.contentURL.href);
	
	::StartRequestData* startRequestData = startRequest->MutableExtension(::StartRequestData::Request);
	startRequestData->set_data(mmiEvent.data);

	return lifeCycleEvent;
}

::LifeCycleEvent MMIProtoBridge::toProto(const StartResponse& mmiEvent) {
	INIT_PROTO_LIFE_CYCLE_EVENT(::LifeCycleEvent_LifeCycleEventType_START_RESPONSE);
	return lifeCycleEvent;
}

::LifeCycleEvent MMIProtoBridge::toProto(const DoneNotification& mmiEvent) {
	INIT_PROTO_LIFE_CYCLE_EVENT(::LifeCycleEvent_LifeCycleEventType_DONE_NOTIFICATION);
	return lifeCycleEvent;
}

::LifeCycleEvent MMIProtoBridge::toProto(const CancelRequest& mmiEvent) {
	INIT_PROTO_LIFE_CYCLE_EVENT(::LifeCycleEvent_LifeCycleEventType_CANCEL_REQUEST);
	return lifeCycleEvent;
}

::LifeCycleEvent MMIProtoBridge::toProto(const CancelResponse& mmiEvent) {
	INIT_PROTO_LIFE_CYCLE_EVENT(::LifeCycleEvent_LifeCycleEventType_CANCEL_RESPONSE);
	return lifeCycleEvent;
}

::LifeCycleEvent MMIProtoBridge::toProto(const PauseRequest& mmiEvent) {
	INIT_PROTO_LIFE_CYCLE_EVENT(::LifeCycleEvent_LifeCycleEventType_PAUSE_REQUEST);
	return lifeCycleEvent;
}

::LifeCycleEvent MMIProtoBridge::toProto(const PauseResponse& mmiEvent) {
	INIT_PROTO_LIFE_CYCLE_EVENT(::LifeCycleEvent_LifeCycleEventType_PAUSE_RESPONSE);
	return lifeCycleEvent;
}

::LifeCycleEvent MMIProtoBridge::toProto(const ResumeRequest& mmiEvent) {
	INIT_PROTO_LIFE_CYCLE_EVENT(::LifeCycleEvent_LifeCycleEventType_RESUME_REQUEST);
	return lifeCycleEvent;
}

::LifeCycleEvent MMIProtoBridge::toProto(const ResumeResponse& mmiEvent) {
	INIT_PROTO_LIFE_CYCLE_EVENT(::LifeCycleEvent_LifeCycleEventType_RESUME_RESPONSE);
	return lifeCycleEvent;
}

::LifeCycleEvent MMIProtoBridge::toProto(const ExtensionNotification& mmiEvent) {
	INIT_PROTO_LIFE_CYCLE_EVENT(::LifeCycleEvent_LifeCycleEventType_EXTENSION_NOTIFICATION);
	return lifeCycleEvent;
}

::LifeCycleEvent MMIProtoBridge::toProto(const ClearContextRequest& mmiEvent) {
	INIT_PROTO_LIFE_CYCLE_EVENT(::LifeCycleEvent_LifeCycleEventType_CLEAR_CONTEXT_REQUEST);
	return lifeCycleEvent;
}

::LifeCycleEvent MMIProtoBridge::toProto(const ClearContextResponse& mmiEvent) {
	INIT_PROTO_LIFE_CYCLE_EVENT(::LifeCycleEvent_LifeCycleEventType_CLEAR_CONTEXT_RESPONSE);
	return lifeCycleEvent;
}

::LifeCycleEvent MMIProtoBridge::toProto(const StatusRequest& mmiEvent) {
	INIT_PROTO_LIFE_CYCLE_EVENT(::LifeCycleEvent_LifeCycleEventType_STATUS_REQUEST);
	return lifeCycleEvent;
}

::LifeCycleEvent MMIProtoBridge::toProto(const StatusResponse& mmiEvent) {
	INIT_PROTO_LIFE_CYCLE_EVENT(::LifeCycleEvent_LifeCycleEventType_STATUS_RESPONSE);
	return lifeCycleEvent;
}

}