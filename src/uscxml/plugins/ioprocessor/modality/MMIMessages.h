#ifndef MMIEVENT_H_OS0SE7H5
#define MMIEVENT_H_OS0SE7H5

#include <DOM/Node.hpp>
#include <DOM/Document.hpp>
#include <uscxml/Interpreter.h>

namespace uscxml {

class MMIEvent {
public:
	enum Type {
	    NEWCONTEXTREQUEST,
	    NEWCONTEXTRESPONSE,
	    PREPAREREQUEST,
	    PREPARERESPONSE,
	    STARTREQUEST,
	    STARTRESPONSE,
	    DONENOTIFICATION,
	    CANCELREQUEST,
	    CANCELRESPONSE,
	    PAUSEREQUEST,
	    PAUSERESPONSE,
	    RESUMEREQUEST,
	    RESUMERESPONSE,
	    EXTENSIONNOTIFICATION,
	    CLEARCONTEXTREQUEST,
	    CLEARCONTEXTRESPONSE,
	    STATUSREQUEST,
	    STATUSRESPONSE,
	    INVALID
	};

	static Type getType(Arabica::DOM::Node<std::string> node);
	static Arabica::DOM::Node<std::string> getEventNode(Arabica::DOM::Node<std::string> node);

	virtual Arabica::DOM::Document<std::string> toXML() const;
	static MMIEvent fromXML(Arabica::DOM::Node<std::string> node,
	                        InterpreterImpl* interpreter = NULL);

	// conversion operator
	operator Event() const;

	std::string source;
	std::string target;
	std::string data;
	std::string requestId;
	std::string tagName;
	Type type;

	static std::string nameSpace;

protected:
	MMIEvent() {}
};

class MMIEventReceiver {
public:
	virtual void received(const MMIEvent& mmiEvent) = 0;
};

class MMIEventSender {
public:
	virtual void send(const MMIEvent& mmiEvent) = 0;
};

class NewContextRequest : public MMIEvent {
public:
	NewContextRequest() {
		tagName = "NewContextRequest";
		type = NEWCONTEXTREQUEST;
	}
	NewContextRequest(const MMIEvent& father) : MMIEvent(father) {}
	static NewContextRequest fromXML(Arabica::DOM::Node<std::string> node,
	                                 InterpreterImpl* interpreter = NULL) {
		MMIEvent event = MMIEvent::fromXML(node, interpreter);
		event.type = NEWCONTEXTREQUEST;
		return event;
	}
	operator Event() const {
		Event ev = MMIEvent::operator Event();
		ev.setName("mmi.newcontextrequest");
		ev.setDOM(toXML());
		return ev;
	}
	std::string token; ///< special token for server-less modality components
};

class ContextualizedRequest : public MMIEvent {
public:
	virtual Arabica::DOM::Document<std::string> toXML() const;
	static ContextualizedRequest fromXML(Arabica::DOM::Node<std::string> node,
	                                     InterpreterImpl* interpreter = NULL);
	operator Event() const;
	std::string context;
protected:
	ContextualizedRequest() {}
	ContextualizedRequest(const MMIEvent& father) : MMIEvent(father) {}
};

class PauseRequest : public ContextualizedRequest {
public:
	PauseRequest() {
		tagName = "PauseRequest";
		type = PAUSEREQUEST;
	}
	PauseRequest(const ContextualizedRequest& father) : ContextualizedRequest(father) {}
	static PauseRequest fromXML(Arabica::DOM::Node<std::string> node,
	                            InterpreterImpl* interpreter = NULL) {
		PauseRequest event = ContextualizedRequest::fromXML(node, interpreter);
		event.type = PAUSEREQUEST;
		return event;
	}
	operator Event() const {
		Event ev = ContextualizedRequest::operator Event();
		ev.setName("mmi.pauserequest");
		ev.setDOM(toXML());
		return ev;
	}

};
class ResumeRequest : public ContextualizedRequest {
public:
	ResumeRequest() {
		tagName = "ResumeRequest";
		type = RESUMEREQUEST;
	}
	ResumeRequest(const ContextualizedRequest& father) : ContextualizedRequest(father) {}
	static ResumeRequest fromXML(Arabica::DOM::Node<std::string> node,
	                             InterpreterImpl* interpreter = NULL) {
		ResumeRequest event = ContextualizedRequest::fromXML(node, interpreter);
		event.type = RESUMEREQUEST;
		return event;
	}
	operator Event() const {
		Event ev = ContextualizedRequest::operator Event();
		ev.setDOM(toXML());
		ev.setName("mmi.resumerequest");
		return ev;
	}

};
class CancelRequest : public ContextualizedRequest {
public:
	CancelRequest() {
		tagName = "CancelRequest";
		type = CANCELREQUEST;
	}
	CancelRequest(const ContextualizedRequest& father) : ContextualizedRequest(father) {}
	static CancelRequest fromXML(Arabica::DOM::Node<std::string> node,
	                             InterpreterImpl* interpreter = NULL) {
		CancelRequest event = ContextualizedRequest::fromXML(node, interpreter);
		event.type = CANCELREQUEST;
		return event;
	}
	operator Event() const {
		Event ev = ContextualizedRequest::operator Event();
		ev.setName("mmi.cancelrequest");
		ev.setDOM(toXML());
		return ev;
	}

};
class ClearContextRequest : public ContextualizedRequest {
public:
	ClearContextRequest() {
		tagName = "ClearContextRequest";
		type = CLEARCONTEXTREQUEST;
	}
	ClearContextRequest(const ContextualizedRequest& father) : ContextualizedRequest(father) {}
	static ClearContextRequest fromXML(Arabica::DOM::Node<std::string> node,
	                                   InterpreterImpl* interpreter = NULL) {
		ClearContextRequest event = ContextualizedRequest::fromXML(node, interpreter);
		event.type = CLEARCONTEXTREQUEST;
		return event;
	}
	operator Event() const {
		Event ev = ContextualizedRequest::operator Event();
		ev.setName("mmi.clearcontextrequest");
		ev.setDOM(toXML());
		return ev;
	}

};
class StatusRequest : public ContextualizedRequest {
public:
	StatusRequest() {
		tagName = "StatusRequest";
		type = STARTREQUEST;
	}
	virtual Arabica::DOM::Document<std::string> toXML() const;
	static StatusRequest fromXML(Arabica::DOM::Node<std::string> node,
	                             InterpreterImpl* interpreter = NULL);
	operator Event() const;
	bool automaticUpdate;
protected:
	StatusRequest(const ContextualizedRequest& father) : ContextualizedRequest(father) {}
};

class ContentRequest : public ContextualizedRequest {
public:
	struct ContentURL {
		std::string href;
		std::string maxAge;
		std::string fetchTimeout;
	};

	virtual Arabica::DOM::Document<std::string> toXML() const;
	static ContentRequest fromXML(Arabica::DOM::Node<std::string> node,
	                              InterpreterImpl* interpreter = NULL);
	operator Event() const;
	std::string content;
	ContentURL contentURL;
protected:
	ContentRequest() {}
	ContentRequest(const ContextualizedRequest& father) : ContextualizedRequest(father) {}
};

class PrepareRequest : public ContentRequest {
public:
	PrepareRequest() {
		tagName = "PrepareRequest";
		type = PREPAREREQUEST;
	}
	PrepareRequest(const ContentRequest& father) : ContentRequest(father) {}
	static PrepareRequest fromXML(Arabica::DOM::Node<std::string> node,
	                              InterpreterImpl* interpreter = NULL) {
		PrepareRequest event = ContentRequest::fromXML(node, interpreter);
		event.type = PREPAREREQUEST;
		return event;
	}
	operator Event() const {
		Event ev = ContentRequest::operator Event();
		ev.setName("mmi.preparerequest");
		ev.setDOM(toXML());
		return ev;
	}
};

class StartRequest : public ContentRequest {
public:
	StartRequest() {
		tagName = "StartRequest";
		type = STARTREQUEST;
	}
	StartRequest(const ContentRequest& father) : ContentRequest(father) {}
	static StartRequest fromXML(Arabica::DOM::Node<std::string> node,
	                            InterpreterImpl* interpreter = NULL) {
		StartRequest event = ContentRequest::fromXML(node, interpreter);
		event.type = STARTREQUEST;
		return event;
	}
	operator Event() const {
		Event ev = ContentRequest::operator Event();
		ev.setName("mmi.startrequest");
		ev.setDOM(toXML());
		return ev;
	}

};

class ExtensionNotification : public ContextualizedRequest {
public:
	ExtensionNotification() {
		tagName = "ExtensionNotification";
		type = EXTENSIONNOTIFICATION;
	}
	virtual Arabica::DOM::Document<std::string> toXML() const;
	static ExtensionNotification fromXML(Arabica::DOM::Node<std::string> node,
	                                     InterpreterImpl* interpreter = NULL);
	operator Event() const;
	std::string name;
protected:
	ExtensionNotification(const ContextualizedRequest& father) : ContextualizedRequest(father) {}

};

class StatusResponse : public ContextualizedRequest {
public:
	enum Status {
	    ALIVE = 0,
	    DEAD = 1,
	    SUCCESS = 2,
	    FAILURE = 3
	};

	StatusResponse() {
		tagName = "StatusResponse";
		type = STATUSRESPONSE;
	}
	virtual Arabica::DOM::Document<std::string> toXML() const;
	static StatusResponse fromXML(Arabica::DOM::Node<std::string> node,
	                              InterpreterImpl* interpreter = NULL);
	Status status;
protected:
	StatusResponse(const ContextualizedRequest& father) : ContextualizedRequest(father) {}
};

class StatusInfoResponse : public StatusResponse {
public:
	virtual Arabica::DOM::Document<std::string> toXML() const;
	StatusInfoResponse(const StatusResponse& father) : StatusResponse(father) {}
	static StatusInfoResponse fromXML(Arabica::DOM::Node<std::string> node,
	                                  InterpreterImpl* interpreter = NULL);
	std::string statusInfo;
protected:
	StatusInfoResponse() {}
};

class PrepareResponse : public StatusInfoResponse {
public:
	PrepareResponse() {
		tagName = "PrepareResponse";
		type = PREPARERESPONSE;
	}
	PrepareResponse(const StatusInfoResponse& father) : StatusInfoResponse(father) {}
	static PrepareResponse fromXML(Arabica::DOM::Node<std::string> node,
	                               InterpreterImpl* interpreter = NULL) {
		PrepareResponse event = StatusInfoResponse::fromXML(node, interpreter);
		event.type = PREPARERESPONSE;
		return event;
	}
	operator Event() const {
		Event ev = StatusInfoResponse::operator Event();
		ev.setName("mmi.prepareresponse");
		ev.setDOM(toXML());
		return ev;
	}
};

class StartResponse : public StatusInfoResponse {
public:
	StartResponse() {
		tagName = "StartResponse";
		type = STARTRESPONSE;
	}
	StartResponse(const StatusInfoResponse& father) : StatusInfoResponse(father) {}
	static StartResponse fromXML(Arabica::DOM::Node<std::string> node,
	                             InterpreterImpl* interpreter = NULL) {
		StartResponse event = StatusInfoResponse::fromXML(node, interpreter);
		event.type = STARTRESPONSE;
		return event;
	}
	operator Event() const {
		Event ev = StatusInfoResponse::operator Event();
		ev.setName("mmi.startresponse");
		ev.setDOM(toXML());
		return ev;
	}
};

class CancelResponse : public StatusInfoResponse {
public:
	CancelResponse() {
		tagName = "CancelResponse";
		type = CANCELRESPONSE;
	}
	CancelResponse(const StatusInfoResponse& father) : StatusInfoResponse(father) {}
	static CancelResponse fromXML(Arabica::DOM::Node<std::string> node,
	                              InterpreterImpl* interpreter = NULL) {
		CancelResponse event = StatusInfoResponse::fromXML(node, interpreter);
		event.type = CANCELRESPONSE;
		return event;
	}
	operator Event() const {
		Event ev = StatusInfoResponse::operator Event();
		ev.setName("mmi.cancelresponse");
		ev.setDOM(toXML());
		return ev;
	}
};

class PauseResponse : public StatusInfoResponse {
public:
	PauseResponse() {
		tagName = "PauseResponse";
		type = PAUSERESPONSE;
	}
	PauseResponse(const StatusInfoResponse& father) : StatusInfoResponse(father) {}
	static PauseResponse fromXML(Arabica::DOM::Node<std::string> node,
	                             InterpreterImpl* interpreter = NULL) {
		PauseResponse event = StatusInfoResponse::fromXML(node, interpreter);
		event.type = PAUSERESPONSE;
		return event;
	}
	operator Event() const {
		Event ev = StatusInfoResponse::operator Event();
		ev.setName("mmi.pauseresponse");
		ev.setDOM(toXML());
		return ev;
	}
};

class ResumeResponse : public StatusInfoResponse {
public:
	ResumeResponse() {
		tagName = "ResumeResponse";
		type = RESUMERESPONSE;
	}
	ResumeResponse(const StatusInfoResponse& father) : StatusInfoResponse(father) {}
	static ResumeResponse fromXML(Arabica::DOM::Node<std::string> node,
	                              InterpreterImpl* interpreter = NULL) {
		ResumeResponse event = StatusInfoResponse::fromXML(node, interpreter);
		event.type = RESUMERESPONSE;
		return event;
	}
	operator Event() const {
		Event ev = StatusInfoResponse::operator Event();
		ev.setName("mmi.resumeresponse");
		ev.setDOM(toXML());
		return ev;
	}
};

class ClearContextResponse : public StatusInfoResponse {
public:
	ClearContextResponse() {
		tagName = "ClearContextResponse";
		type = CLEARCONTEXTRESPONSE;
	}
	ClearContextResponse(const StatusInfoResponse& father) : StatusInfoResponse(father) {}
	static ClearContextResponse fromXML(Arabica::DOM::Node<std::string> node,
	                                    InterpreterImpl* interpreter = NULL) {
		ClearContextResponse event = StatusInfoResponse::fromXML(node, interpreter);
		event.type = CLEARCONTEXTRESPONSE;
		return event;
	}
	operator Event() const {
		Event ev = StatusInfoResponse::operator Event();
		ev.setName("mmi.clearcontextresponse");
		ev.setDOM(toXML());
		return ev;
	}
};

class NewContextResponse : public StatusInfoResponse {
public:
	NewContextResponse() {
		tagName = "NewContextResponse";
		type = NEWCONTEXTRESPONSE;
	}
	NewContextResponse(const StatusInfoResponse& father) : StatusInfoResponse(father) {}
	static NewContextResponse fromXML(Arabica::DOM::Node<std::string> node,
	                                  InterpreterImpl* interpreter = NULL) {
		NewContextResponse event = StatusInfoResponse::fromXML(node, interpreter);
		event.type = NEWCONTEXTRESPONSE;
		return event;
	}
	operator Event() const {
		Event ev = StatusInfoResponse::operator Event();
		ev.setName("mmi.newcontextresponse");
		ev.setDOM(toXML());
		return ev;
	}

};

class DoneNotification : public StatusInfoResponse {
public:
	DoneNotification() {
		tagName = "DoneNotification";
		type = DONENOTIFICATION;
	}
	DoneNotification(const StatusInfoResponse& father) : StatusInfoResponse(father) {}
	static DoneNotification fromXML(Arabica::DOM::Node<std::string> node,
	                                InterpreterImpl* interpreter = NULL) {
		DoneNotification event = StatusInfoResponse::fromXML(node, interpreter);
		event.type = DONENOTIFICATION;
		return event;
	}
	operator Event() const {
		Event ev = StatusInfoResponse::operator Event();
		ev.setName("mmi.donenotification");
		ev.setDOM(toXML());
		return ev;
	}
};

}

#endif /* end of include guard: MMIEVENT_H_OS0SE7H5 */
