#ifndef MMIMESSAGES_H_OS0SE7H5
#define MMIMESSAGES_H_OS0SE7H5

#include <DOM/Node.hpp>
#include <DOM/Document.hpp>

namespace uscxml {

class MMIMessage {
public:
	virtual Arabica::DOM::Document<std::string> toXML();
	static MMIMessage fromXML(const Arabica::DOM::Document<std::string>& doc);

	std::string source;
	std::string target;
	std::string data;
	std::string requestId;
	std::string tagName;

	static std::string nameSpace;

protected:
	MMIMessage() {}
};

class NewContextRequest : public MMIMessage {
public:
	NewContextRequest() {
		tagName = "NewContextRequest";
	}
	NewContextRequest(const MMIMessage& father) : MMIMessage(father) {}
	static NewContextRequest fromXML(const Arabica::DOM::Document<std::string>& doc) {
		return MMIMessage::fromXML(doc);
	}

};

class ContextualizedRequest : public NewContextRequest {
public:
	virtual Arabica::DOM::Document<std::string> toXML();
	static ContextualizedRequest fromXML(const Arabica::DOM::Document<std::string>& doc);

	std::string context;
protected:
	ContextualizedRequest() {}
	ContextualizedRequest(const NewContextRequest& father) : NewContextRequest(father) {}
};

class PauseRequest : public ContextualizedRequest {
public:
	PauseRequest() {
		tagName = "PauseRequest";
	}
	PauseRequest(const ContextualizedRequest& father) : ContextualizedRequest(father) {}
	static PauseRequest fromXML(const Arabica::DOM::Document<std::string>& doc) {
		return ContextualizedRequest::fromXML(doc);
	}
};
class ResumeRequest : public ContextualizedRequest {
public:
	ResumeRequest() {
		tagName = "ResumeRequest";
	}
	ResumeRequest(const ContextualizedRequest& father) : ContextualizedRequest(father) {}
	static ResumeRequest fromXML(const Arabica::DOM::Document<std::string>& doc) {
		return ContextualizedRequest::fromXML(doc);
	}

};
class CancelRequest : public ContextualizedRequest {
public:
	CancelRequest() {
		tagName = "CancelRequest";
	}
	CancelRequest(const ContextualizedRequest& father) : ContextualizedRequest(father) {}
	static CancelRequest fromXML(const Arabica::DOM::Document<std::string>& doc) {
		return ContextualizedRequest::fromXML(doc);
	}

};
class ClearContextRequest : public ContextualizedRequest {
public:
	ClearContextRequest() {
		tagName = "ClearContextRequest";
	}
	ClearContextRequest(const ContextualizedRequest& father) : ContextualizedRequest(father) {}
	static ClearContextRequest fromXML(const Arabica::DOM::Document<std::string>& doc) {
		return ContextualizedRequest::fromXML(doc);
	}

};
class StatusRequest : public ContextualizedRequest {
public:
	StatusRequest() {
		tagName = "StatusRequest";
	}
	virtual Arabica::DOM::Document<std::string> toXML();
	static StatusRequest fromXML(const Arabica::DOM::Document<std::string>& doc);

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

	virtual Arabica::DOM::Document<std::string> toXML();
	static ContentRequest fromXML(const Arabica::DOM::Document<std::string>& doc);
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
	}
	PrepareRequest(const ContentRequest& father) : ContentRequest(father) {}
	static PrepareRequest fromXML(const Arabica::DOM::Document<std::string>& doc) {
		return ContentRequest::fromXML(doc);
	}
};

class StartRequest : public ContentRequest {
public:
	StartRequest() {
		tagName = "StartRequest";
	}
	StartRequest(const ContentRequest& father) : ContentRequest(father) {}
	static StartRequest fromXML(const Arabica::DOM::Document<std::string>& doc) {
		return ContentRequest::fromXML(doc);
	}

};

class ExtensionNotification : public ContextualizedRequest {
public:
	ExtensionNotification() {
		tagName = "ExtensionNotification";
	}
	virtual Arabica::DOM::Document<std::string> toXML();
	static ExtensionNotification fromXML(const Arabica::DOM::Document<std::string>& doc);

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
	}
	virtual Arabica::DOM::Document<std::string> toXML();
	static StatusResponse fromXML(const Arabica::DOM::Document<std::string>& doc);
	Status status;
protected:
	StatusResponse(const ContextualizedRequest& father) : ContextualizedRequest(father) {}

};

class StatusInfoResponse : public StatusResponse {
public:
	virtual Arabica::DOM::Document<std::string> toXML();
	static StatusInfoResponse fromXML(const Arabica::DOM::Document<std::string>& doc);
	std::string statusInfo;
protected:
	StatusInfoResponse() {}
	StatusInfoResponse(const StatusResponse& father) : StatusResponse(father) {}
};

class PrepareResponse : public StatusInfoResponse {
public:
	PrepareResponse() {
		tagName = "PrepareResponse";
	}
	PrepareResponse(const StatusInfoResponse& father) : StatusInfoResponse(father) {}
	static PrepareResponse fromXML(const Arabica::DOM::Document<std::string>& doc) {
		return StatusInfoResponse::fromXML(doc);
	}
};

class StartResponse : public StatusInfoResponse {
public:
	StartResponse() {
		tagName = "StartResponse";
	}
	StartResponse(const StatusInfoResponse& father) : StatusInfoResponse(father) {}
	static StartResponse fromXML(const Arabica::DOM::Document<std::string>& doc) {
		return StatusInfoResponse::fromXML(doc);
	}
};

class CancelResponse : public StatusInfoResponse {
public:
	CancelResponse() {
		tagName = "CancelResponse";
	}
	CancelResponse(const StatusInfoResponse& father) : StatusInfoResponse(father) {}
	static CancelResponse fromXML(const Arabica::DOM::Document<std::string>& doc) {
		return StatusInfoResponse::fromXML(doc);
	}
};

class PauseResponse : public StatusInfoResponse {
public:
	PauseResponse() {
		tagName = "PauseResponse";
	}
	PauseResponse(const StatusInfoResponse& father) : StatusInfoResponse(father) {}
	static PauseResponse fromXML(const Arabica::DOM::Document<std::string>& doc) {
		return StatusInfoResponse::fromXML(doc);
	}
};

class ResumeResponse : public StatusInfoResponse {
public:
	ResumeResponse() {
		tagName = "ResumeResponse";
	}
	ResumeResponse(const StatusInfoResponse& father) : StatusInfoResponse(father) {}
	static ResumeResponse fromXML(const Arabica::DOM::Document<std::string>& doc) {
		return StatusInfoResponse::fromXML(doc);
	}
};

class ClearContextResponse : public StatusInfoResponse {
public:
	ClearContextResponse() {
		tagName = "ClearContextResponse";
	}
	ClearContextResponse(const StatusInfoResponse& father) : StatusInfoResponse(father) {}
	static ClearContextResponse fromXML(const Arabica::DOM::Document<std::string>& doc) {
		return StatusInfoResponse::fromXML(doc);
	}
};

class NewContextResponse : public StatusInfoResponse {
public:
	NewContextResponse() {
		tagName = "NewContextResponse";
	}
	NewContextResponse(const StatusInfoResponse& father) : StatusInfoResponse(father) {}
	static NewContextResponse fromXML(const Arabica::DOM::Document<std::string>& doc) {
		return StatusInfoResponse::fromXML(doc);
	}

};

class DoneNotification : public StatusInfoResponse {
public:
	DoneNotification() {
		tagName = "DoneNotification";
	}
	DoneNotification(const StatusInfoResponse& father) : StatusInfoResponse(father) {}
	static DoneNotification fromXML(const Arabica::DOM::Document<std::string>& doc) {
		return StatusInfoResponse::fromXML(doc);
	}
};

}

#endif /* end of include guard: MMIMESSAGES_H_OS0SE7H5 */
