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

#ifndef MMIEVENT_H_OS0SE7H5
#define MMIEVENT_H_OS0SE7H5

#define MMI_WITH_OPERATOR_EVENT 1

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

	enum RepresentationType {
		MMI_AS_DATA,
		MMI_AS_XML
	};
	static Type getType(Arabica::DOM::Node<std::string> node);

	virtual Arabica::DOM::Document<std::string> toXML(bool encapsulateInMMI = true) const;
	static MMIEvent fromXML(Arabica::DOM::Node<std::string> node, InterpreterImpl* interpreter = NULL);

#ifdef MMI_WITH_OPERATOR_EVENT
	// conversion operator
	operator Event() const;
#endif

	std::string source;
	std::string target;
	std::string data;
	Arabica::DOM::Node<std::string> dataDOM;
	std::string requestId;

	std::string tagName;
	Type type;
	RepresentationType representation;

	static std::string nameSpace;

protected:
	MMIEvent() : representation(MMI_AS_DATA) {}
};

class NewContextRequest : public MMIEvent {
public:
	NewContextRequest() {
		tagName = "NewContextRequest";
		type = NEWCONTEXTREQUEST;
	}
	NewContextRequest(const MMIEvent& father) : MMIEvent(father) {}
	static NewContextRequest fromXML(Arabica::DOM::Node<std::string> node, InterpreterImpl* interpreter = NULL);

#ifdef MMI_WITH_OPERATOR_EVENT
	operator Event() const;
#endif

	std::string token; ///< special token for server-less modality components
};

class ContextualizedRequest : public MMIEvent {
public:
	virtual Arabica::DOM::Document<std::string> toXML(bool encapsulateInMMI = true) const;
	static ContextualizedRequest fromXML(Arabica::DOM::Node<std::string> node, InterpreterImpl* interpreter = NULL);

#ifdef MMI_WITH_OPERATOR_EVENT
	operator Event() const;
#endif

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
	static PauseRequest fromXML(Arabica::DOM::Node<std::string> node, InterpreterImpl* interpreter = NULL);

#ifdef MMI_WITH_OPERATOR_EVENT
	operator Event() const;
#endif

};
class ResumeRequest : public ContextualizedRequest {
public:
	ResumeRequest() {
		tagName = "ResumeRequest";
		type = RESUMEREQUEST;
	}
	ResumeRequest(const ContextualizedRequest& father) : ContextualizedRequest(father) {}
	static ResumeRequest fromXML(Arabica::DOM::Node<std::string> node, InterpreterImpl* interpreter = NULL);

#ifdef MMI_WITH_OPERATOR_EVENT
	operator Event() const;
#endif

};
class CancelRequest : public ContextualizedRequest {
public:
	CancelRequest() {
		tagName = "CancelRequest";
		type = CANCELREQUEST;
	}
	CancelRequest(const ContextualizedRequest& father) : ContextualizedRequest(father) {}
	static CancelRequest fromXML(Arabica::DOM::Node<std::string> node, InterpreterImpl* interpreter = NULL);

#ifdef MMI_WITH_OPERATOR_EVENT
	operator Event() const;
#endif

};
class ClearContextRequest : public ContextualizedRequest {
public:
	ClearContextRequest() {
		tagName = "ClearContextRequest";
		type = CLEARCONTEXTREQUEST;
	}
	ClearContextRequest(const ContextualizedRequest& father) : ContextualizedRequest(father) {}
	static ClearContextRequest fromXML(Arabica::DOM::Node<std::string> node, InterpreterImpl* interpreter = NULL);

#ifdef MMI_WITH_OPERATOR_EVENT
	operator Event() const;
#endif

};
class StatusRequest : public ContextualizedRequest {
public:
	StatusRequest() {
		tagName = "StatusRequest";
		type = STARTREQUEST;
	}
	virtual Arabica::DOM::Document<std::string> toXML(bool encapsulateInMMI = true) const;
	static StatusRequest fromXML(Arabica::DOM::Node<std::string> node, InterpreterImpl* interpreter = NULL);

#ifdef MMI_WITH_OPERATOR_EVENT
	operator Event() const;
#endif

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

	virtual Arabica::DOM::Document<std::string> toXML(bool encapsulateInMMI = true) const;
	static ContentRequest fromXML(Arabica::DOM::Node<std::string> node, InterpreterImpl* interpreter = NULL);

#ifdef MMI_WITH_OPERATOR_EVENT
	operator Event() const;
#endif

	std::string content;
	Arabica::DOM::Node<std::string> contentDOM;
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
	static PrepareRequest fromXML(Arabica::DOM::Node<std::string> node, InterpreterImpl* interpreter = NULL);

#ifdef MMI_WITH_OPERATOR_EVENT
	operator Event() const;
#endif
};

class StartRequest : public ContentRequest {
public:
	StartRequest() {
		tagName = "StartRequest";
		type = STARTREQUEST;
	}
	StartRequest(const ContentRequest& father) : ContentRequest(father) {}
	static StartRequest fromXML(Arabica::DOM::Node<std::string> node, InterpreterImpl* interpreter = NULL);

#ifdef MMI_WITH_OPERATOR_EVENT
	operator Event() const;
#endif

};

class ExtensionNotification : public ContextualizedRequest {
public:
	ExtensionNotification() {
		tagName = "ExtensionNotification";
		type = EXTENSIONNOTIFICATION;
	}
	virtual Arabica::DOM::Document<std::string> toXML(bool encapsulateInMMI = true) const;
	static ExtensionNotification fromXML(Arabica::DOM::Node<std::string> node, InterpreterImpl* interpreter = NULL);

#ifdef MMI_WITH_OPERATOR_EVENT
	operator Event() const;
#endif

	std::string name;
protected:
	ExtensionNotification(const ContextualizedRequest& father) : ContextualizedRequest(father) {}

};

class StatusResponse : public ContextualizedRequest {
public:
	enum Status {
		INVALID = 0,
		ALIVE = 1,
		DEAD = 2,
		SUCCESS = 3,
		FAILURE = 4
	};

	StatusResponse() {
		tagName = "StatusResponse";
		type = STATUSRESPONSE;
		status = INVALID;
	}
	virtual Arabica::DOM::Document<std::string> toXML(bool encapsulateInMMI = true) const;
	static StatusResponse fromXML(Arabica::DOM::Node<std::string> node, InterpreterImpl* interpreter = NULL);

#ifdef MMI_WITH_OPERATOR_EVENT
	operator Event() const;
#endif

	Status status;
protected:
	StatusResponse(const ContextualizedRequest& father) : ContextualizedRequest(father) {}
};

class StatusInfoResponse : public StatusResponse {
public:
	virtual Arabica::DOM::Document<std::string> toXML(bool encapsulateInMMI = true) const;
	StatusInfoResponse(const StatusResponse& father) : StatusResponse(father) {}
	static StatusInfoResponse fromXML(Arabica::DOM::Node<std::string> node, InterpreterImpl* interpreter = NULL);
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
	static PrepareResponse fromXML(Arabica::DOM::Node<std::string> node, InterpreterImpl* interpreter = NULL);

#ifdef MMI_WITH_OPERATOR_EVENT
	operator Event() const;
#endif

};

class StartResponse : public StatusInfoResponse {
public:
	StartResponse() {
		tagName = "StartResponse";
		type = STARTRESPONSE;
	}
	StartResponse(const StatusInfoResponse& father) : StatusInfoResponse(father) {}
	static StartResponse fromXML(Arabica::DOM::Node<std::string> node, InterpreterImpl* interpreter = NULL);

#ifdef MMI_WITH_OPERATOR_EVENT
	operator Event() const;
#endif
};

class CancelResponse : public StatusInfoResponse {
public:
	CancelResponse() {
		tagName = "CancelResponse";
		type = CANCELRESPONSE;
	}
	CancelResponse(const StatusInfoResponse& father) : StatusInfoResponse(father) {}
	static CancelResponse fromXML(Arabica::DOM::Node<std::string> node, InterpreterImpl* interpreter = NULL);

#ifdef MMI_WITH_OPERATOR_EVENT
	operator Event() const;
#endif
};

class PauseResponse : public StatusInfoResponse {
public:
	PauseResponse() {
		tagName = "PauseResponse";
		type = PAUSERESPONSE;
	}
	PauseResponse(const StatusInfoResponse& father) : StatusInfoResponse(father) {}
	static PauseResponse fromXML(Arabica::DOM::Node<std::string> node, InterpreterImpl* interpreter = NULL);

#ifdef MMI_WITH_OPERATOR_EVENT
	operator Event() const;
#endif
};

class ResumeResponse : public StatusInfoResponse {
public:
	ResumeResponse() {
		tagName = "ResumeResponse";
		type = RESUMERESPONSE;
	}
	ResumeResponse(const StatusInfoResponse& father) : StatusInfoResponse(father) {}
	static ResumeResponse fromXML(Arabica::DOM::Node<std::string> node, InterpreterImpl* interpreter = NULL);

#ifdef MMI_WITH_OPERATOR_EVENT
	operator Event() const;
#endif
};

class ClearContextResponse : public StatusInfoResponse {
public:
	ClearContextResponse() {
		tagName = "ClearContextResponse";
		type = CLEARCONTEXTRESPONSE;
	}
	ClearContextResponse(const StatusInfoResponse& father) : StatusInfoResponse(father) {}
	static ClearContextResponse fromXML(Arabica::DOM::Node<std::string> node, InterpreterImpl* interpreter = NULL);

#ifdef MMI_WITH_OPERATOR_EVENT
	operator Event() const;
#endif
};

class NewContextResponse : public StatusInfoResponse {
public:
	NewContextResponse() {
		tagName = "NewContextResponse";
		type = NEWCONTEXTRESPONSE;
	}
	NewContextResponse(const StatusInfoResponse& father) : StatusInfoResponse(father) {}
	static NewContextResponse fromXML(Arabica::DOM::Node<std::string> node, InterpreterImpl* interpreter = NULL);

#ifdef MMI_WITH_OPERATOR_EVENT
	operator Event() const;
#endif
};

class DoneNotification : public StatusInfoResponse {
public:
	DoneNotification() {
		tagName = "DoneNotification";
		type = DONENOTIFICATION;
	}
	DoneNotification(const StatusInfoResponse& father) : StatusInfoResponse(father) {}
	static DoneNotification fromXML(Arabica::DOM::Node<std::string> node, InterpreterImpl* interpreter = NULL);

#ifdef MMI_WITH_OPERATOR_EVENT
	operator Event() const;
#endif
};

}

#endif /* end of include guard: MMIEVENT_H_OS0SE7H5 */
