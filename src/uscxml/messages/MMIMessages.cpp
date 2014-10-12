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

#include <string> // MSVC will croak with operator+ on strings if this is not first

#include "MMIMessages.h"

#include <DOM/Simple/DOMImplementation.hpp>
#include <DOM/io/Stream.hpp>
#include <DOM/SAX2DOM/SAX2DOM.hpp>
#include <SAX/helpers/InputSourceResolver.hpp>

#include <uscxml/DOMUtils.h>

#include <boost/algorithm/string.hpp>

#define TO_EVENT_OPERATOR(type, name, base)\
type::operator Event() const { \
	Event ev = base::operator Event();\
	ev.setName(name);\
	if (representation == MMI_AS_XML) \
		ev.setDOM(toXML());\
	return ev;\
}

#define FIND_MSG_ELEM(elem, doc) \
Element<std::string> elem; \
if (encapsulateInMMI) { \
	elem = Element<std::string>(doc.getDocumentElement().getFirstChild()); \
} else { \
	elem = Element<std::string>(doc.getDocumentElement()); \
}

#define FROM_XML(clazz, enumType, base) \
clazz clazz::fromXML(Arabica::DOM::Node<std::string> node, InterpreterImpl* interpreter) { \
	clazz event = base::fromXML(node, interpreter); \
	event.type = enumType; \
	return event; \
}

#define STRING_ATTR_OR_EXPR(element, name)\
(element.hasAttributeNS(nameSpace, "name##Expr") && interpreter ? \
	interpreter->getDataModel().evalAsString(element.getAttributeNS(nameSpace, "name##Expr")) : \
	(element.hasAttributeNS(nameSpace, #name) ? element.getAttributeNS(nameSpace, #name) : "") \
)

#define FIND_EVENT_NODE(node)\
if (node.getNodeType() == Node_base::DOCUMENT_NODE) \
	node = node.getFirstChild(); \
while (node) {\
	if (node.getNodeType() == Node_base::ELEMENT_NODE) {\
		if (boost::iequals(node.getLocalName(), "MMI")) {\
			node = node.getFirstChild();\
			continue;\
		} else {\
			break;\
		}\
	}\
	node = node.getNextSibling();\
}\
 

namespace uscxml {

using namespace Arabica::DOM;

std::string MMIEvent::nameSpace = "http://www.w3.org/2008/04/mmi-arch";

MMIEvent::Type MMIEvent::getType(Arabica::DOM::Node<std::string> node) {
	if (!node || node.getNodeType() != Arabica::DOM::Node_base::ELEMENT_NODE)
		return INVALID;

	// MMI container?
	if (boost::iequals(node.getLocalName(), "MMI")) {
		node = node.getFirstChild();
		if (!node)
			return INVALID;
		while(node.getNodeType() != Arabica::DOM::Node_base::ELEMENT_NODE) {
			node = node.getNextSibling();
			if (!node)
				return INVALID;
		}
	}

	if (boost::iequals(node.getLocalName(), "NEWCONTEXTREQUEST"))
		return NEWCONTEXTREQUEST;
	if (boost::iequals(node.getLocalName(), "NEWCONTEXTRESPONSE"))
		return NEWCONTEXTRESPONSE;
	if (boost::iequals(node.getLocalName(), "PREPAREREQUEST"))
		return PREPAREREQUEST;
	if (boost::iequals(node.getLocalName(), "PREPARERESPONSE"))
		return PREPARERESPONSE;
	if (boost::iequals(node.getLocalName(), "STARTREQUEST"))
		return STARTREQUEST;
	if (boost::iequals(node.getLocalName(), "STARTRESPONSE"))
		return STARTRESPONSE;
	if (boost::iequals(node.getLocalName(), "DONENOTIFICATION"))
		return DONENOTIFICATION;
	if (boost::iequals(node.getLocalName(), "CANCELREQUEST"))
		return CANCELREQUEST;
	if (boost::iequals(node.getLocalName(), "CANCELRESPONSE"))
		return CANCELRESPONSE;
	if (boost::iequals(node.getLocalName(), "PAUSEREQUEST"))
		return PAUSEREQUEST;
	if (boost::iequals(node.getLocalName(), "PAUSERESPONSE"))
		return PAUSERESPONSE;
	if (boost::iequals(node.getLocalName(), "RESUMEREQUEST"))
		return RESUMEREQUEST;
	if (boost::iequals(node.getLocalName(), "RESUMERESPONSE"))
		return RESUMERESPONSE;
	if (boost::iequals(node.getLocalName(), "EXTENSIONNOTIFICATION"))
		return EXTENSIONNOTIFICATION;
	if (boost::iequals(node.getLocalName(), "CLEARCONTEXTREQUEST"))
		return CLEARCONTEXTREQUEST;
	if (boost::iequals(node.getLocalName(), "CLEARCONTEXTRESPONSE"))
		return CLEARCONTEXTRESPONSE;
	if (boost::iequals(node.getLocalName(), "STATUSREQUEST"))
		return STATUSREQUEST;
	if (boost::iequals(node.getLocalName(), "STATUSRESPONSE"))
		return STATUSRESPONSE;
	return INVALID;
}

Arabica::DOM::Document<std::string> MMIEvent::toXML(bool encapsulateInMMI) const {
	Arabica::DOM::DOMImplementation<std::string> domFactory = Arabica::SimpleDOM::DOMImplementation<std::string>::getDOMImplementation();
	Document<std::string> doc = domFactory.createDocument(nameSpace, "", 0);
	Element<std::string> msgElem = doc.createElementNS(nameSpace, tagName);
	msgElem.setAttributeNS(nameSpace, "Source", source);
	msgElem.setAttributeNS(nameSpace, "Target", target);
	msgElem.setAttributeNS(nameSpace, "RequestID", requestId);

	if (dataDOM) {
		Element<std::string> dataElem = doc.createElementNS(nameSpace, "Data");
		Node<std::string> importNode = doc.importNode(dataDOM, true);
		dataElem.appendChild(importNode);
		msgElem.appendChild(dataElem);
	}	else if (data.size() > 0) {
		Element<std::string> dataElem = doc.createElementNS(nameSpace, "Data");
		Text<std::string> textElem = doc.createTextNode(data);
		dataElem.appendChild(textElem);
		msgElem.appendChild(dataElem);
	}

	if (encapsulateInMMI) {
		Element<std::string> mmiElem = doc.createElementNS(nameSpace, "mmi");
		mmiElem.appendChild(msgElem);
		doc.appendChild(mmiElem);
	} else {
		doc.appendChild(msgElem);
	}
	return doc;
}

Arabica::DOM::Document<std::string> ContentRequest::toXML(bool encapsulateInMMI) const {
	Document<std::string> doc = ContextualizedRequest::toXML(encapsulateInMMI);
	FIND_MSG_ELEM(msgElem, doc);

	if (contentURL.href.size() > 0) {
		Element<std::string> contentURLElem = doc.createElementNS(nameSpace, "ContentURL");
		contentURLElem.setAttributeNS(nameSpace, "href", contentURL.href);
		contentURLElem.setAttributeNS(nameSpace, "fetchtimeout", contentURL.fetchTimeout);
		contentURLElem.setAttributeNS(nameSpace, "max-age", contentURL.maxAge);
		msgElem.appendChild(contentURLElem);
	} else if (contentDOM) {
		Element<std::string> contentElem = doc.createElementNS(nameSpace, "Content");
		Node<std::string> importNode = doc.importNode(contentDOM, true);
		contentElem.appendChild(importNode);
		msgElem.appendChild(contentElem);
	} else if (content.size() > 0) {
		Element<std::string> contentElem = doc.createElementNS(nameSpace, "Content");
		Text<std::string> textElem = doc.createTextNode(content);
		contentElem.appendChild(textElem);
		msgElem.appendChild(contentElem);
	}
	return doc;
}

Arabica::DOM::Document<std::string> ContextualizedRequest::toXML(bool encapsulateInMMI) const {
	Document<std::string> doc = MMIEvent::toXML(encapsulateInMMI);
	FIND_MSG_ELEM(msgElem, doc);
	msgElem.setAttributeNS(nameSpace, "Context", context);
	return doc;
}

Arabica::DOM::Document<std::string> ExtensionNotification::toXML(bool encapsulateInMMI) const {
	Document<std::string> doc = ContextualizedRequest::toXML(encapsulateInMMI);
	FIND_MSG_ELEM(msgElem, doc);
	msgElem.setAttributeNS(nameSpace, "Name", name);
	return doc;
}

Arabica::DOM::Document<std::string> StatusResponse::toXML(bool encapsulateInMMI) const {
	Document<std::string> doc = ContextualizedRequest::toXML(encapsulateInMMI);
	FIND_MSG_ELEM(msgElem, doc);
	if (status == ALIVE) {
		msgElem.setAttributeNS(nameSpace, "Status", "alive");
	} else if(status == DEAD) {
		msgElem.setAttributeNS(nameSpace, "Status", "dead");
	} else if(status == FAILURE) {
		msgElem.setAttributeNS(nameSpace, "Status", "failure");
	} else if(status == SUCCESS) {
		msgElem.setAttributeNS(nameSpace, "Status", "success");
	}
	return doc;
}

Arabica::DOM::Document<std::string> StatusInfoResponse::toXML(bool encapsulateInMMI) const {
	Document<std::string> doc = StatusResponse::toXML(encapsulateInMMI);
	FIND_MSG_ELEM(msgElem, doc);

	Element<std::string> statusInfoElem = doc.createElementNS(nameSpace, "StatusInfo");
	Text<std::string> statusInfoText = doc.createTextNode(statusInfo);
	statusInfoElem.appendChild(statusInfoText);
	msgElem.appendChild(statusInfoElem);

	return doc;
}

Arabica::DOM::Document<std::string> StatusRequest::toXML(bool encapsulateInMMI) const {
	Document<std::string> doc = ContextualizedRequest::toXML(encapsulateInMMI);
	FIND_MSG_ELEM(msgElem, doc);

	if (automaticUpdate) {
		msgElem.setAttributeNS(nameSpace, "RequestAutomaticUpdate", "true");
	} else {
		msgElem.setAttributeNS(nameSpace, "RequestAutomaticUpdate", "false");
	}

	return doc;
}



MMIEvent MMIEvent::fromXML(Arabica::DOM::Node<std::string> node, InterpreterImpl* interpreter) {
	MMIEvent msg;

	FIND_EVENT_NODE(node);

	Element<std::string> msgElem(node);
	msg.source = STRING_ATTR_OR_EXPR(msgElem, Source);
	msg.target = STRING_ATTR_OR_EXPR(msgElem, Target);
	msg.requestId = STRING_ATTR_OR_EXPR(msgElem, RequestID);
	msg.tagName = msgElem.getLocalName();

	Element<std::string> dataElem;

	// search for data element
	node = msgElem.getFirstChild();
	while (node) {
		if (node.getNodeType() == Node_base::ELEMENT_NODE)
			dataElem = Element<std::string>(node);
		if (dataElem && boost::iequals(dataElem.getLocalName(), "data"))
			break;
		node = node.getNextSibling();
	}

	if (dataElem && boost::iequals(dataElem.getLocalName(), "data") && dataElem.getFirstChild()) {
		Arabica::DOM::Node<std::string> dataChild = dataElem.getFirstChild();
		std::stringstream ss;

		while (dataChild) {
			if (dataChild.getNodeType() == Arabica::DOM::Node_base::ELEMENT_NODE)
				msg.dataDOM = dataChild;
			ss << dataChild;
			dataChild = dataChild.getNextSibling();
		}
		msg.data = ss.str();
	}

	return msg;
}

FROM_XML(NewContextRequest,    NEWCONTEXTREQUEST,    MMIEvent)

FROM_XML(PauseRequest,         PAUSEREQUEST,         ContextualizedRequest)
FROM_XML(ResumeRequest,        RESUMEREQUEST,        ContextualizedRequest)
FROM_XML(ClearContextRequest,  CLEARCONTEXTREQUEST,  ContextualizedRequest)
FROM_XML(CancelRequest,        CANCELREQUEST,        ContextualizedRequest)

FROM_XML(PrepareRequest,       PREPAREREQUEST,       ContentRequest)
FROM_XML(StartRequest,         STARTREQUEST,         ContentRequest)

FROM_XML(PrepareResponse,      PREPARERESPONSE,      StatusInfoResponse)
FROM_XML(StartResponse,        STARTRESPONSE,        StatusInfoResponse)
FROM_XML(CancelResponse,       CANCELRESPONSE,       StatusInfoResponse)
FROM_XML(PauseResponse,        PAUSERESPONSE,        StatusInfoResponse)
FROM_XML(ResumeResponse,       RESUMERESPONSE,       StatusInfoResponse)
FROM_XML(ClearContextResponse, CLEARCONTEXTRESPONSE, StatusInfoResponse)
FROM_XML(NewContextResponse,   NEWCONTEXTRESPONSE,   StatusInfoResponse)
FROM_XML(DoneNotification,     DONENOTIFICATION,     StatusInfoResponse)


ContextualizedRequest ContextualizedRequest::fromXML(Arabica::DOM::Node<std::string> node, InterpreterImpl* interpreter) {
	ContextualizedRequest msg(MMIEvent::fromXML(node, interpreter));
	FIND_EVENT_NODE(node);

	Element<std::string> msgElem(node);
	msg.context = STRING_ATTR_OR_EXPR(msgElem, Context);
	return msg;
}

ExtensionNotification ExtensionNotification::fromXML(Arabica::DOM::Node<std::string> node, InterpreterImpl* interpreter) {
	ExtensionNotification msg(ContextualizedRequest::fromXML(node, interpreter));
	FIND_EVENT_NODE(node);

	Element<std::string> msgElem(node);
	msg.name = STRING_ATTR_OR_EXPR(msgElem, Name);
	msg.type = EXTENSIONNOTIFICATION;
	return msg;
}

ContentRequest ContentRequest::fromXML(Arabica::DOM::Node<std::string> node, InterpreterImpl* interpreter) {
	ContentRequest msg(ContextualizedRequest::fromXML(node, interpreter));
	FIND_EVENT_NODE(node);

	Element<std::string> msgElem(node);
	Element<std::string> contentElem;

	node = msgElem.getFirstChild();
	while (node) {
		if (node.getNodeType() == Node_base::ELEMENT_NODE) {
			contentElem = Element<std::string>(node);
			if (boost::iequals(contentElem.getLocalName(), "content") ||
			        boost::iequals(contentElem.getLocalName(), "contentURL"))
				break;
		}
		node = node.getNextSibling();
	}

	if (contentElem) {
		if(boost::iequals(contentElem.getLocalName(), "content")) {
			Arabica::DOM::Node<std::string> contentChild = contentElem.getFirstChild();
			std::stringstream ss;

			while (contentChild) {
				if (contentChild.getNodeType() == Arabica::DOM::Node_base::ELEMENT_NODE)
					msg.contentDOM = contentChild;
				ss << contentChild;
				contentChild = contentChild.getNextSibling();
			}
			msg.content = ss.str();

		} else if(boost::iequals(contentElem.getLocalName(), "contentURL")) {
			msg.contentURL.href = STRING_ATTR_OR_EXPR(contentElem, href);
			msg.contentURL.maxAge = STRING_ATTR_OR_EXPR(contentElem, max-age);
			msg.contentURL.fetchTimeout = STRING_ATTR_OR_EXPR(contentElem, fetchtimeout);
		}
	}

	//msg.content = msgElem.getAttributeNS(nameSpace, "Context");
	return msg;
}

StatusResponse StatusResponse::fromXML(Arabica::DOM::Node<std::string> node, InterpreterImpl* interpreter) {
	StatusResponse msg(ContextualizedRequest::fromXML(node, interpreter));
	FIND_EVENT_NODE(node);

	Element<std::string> msgElem(node);
	std::string status = STRING_ATTR_OR_EXPR(msgElem, Status);

	if (boost::iequals(status, "ALIVE")) {
		msg.status = ALIVE;
	} else if(boost::iequals(status, "DEAD")) {
		msg.status = DEAD;
	} else if(boost::iequals(status, "FAILURE")) {
		msg.status = FAILURE;
	} else if(boost::iequals(status, "SUCCESS")) {
		msg.status = SUCCESS;
	} else {
		msg.status = INVALID;
	}
	msg.type = STATUSRESPONSE;
	return msg;
}

StatusInfoResponse StatusInfoResponse::fromXML(Arabica::DOM::Node<std::string> node, InterpreterImpl* interpreter) {
	StatusInfoResponse msg(StatusResponse::fromXML(node, interpreter));
	FIND_EVENT_NODE(node);

	Element<std::string> msgElem(node);
	Element<std::string> statusInfoElem;

	node = msgElem.getFirstChild();
	while (node) {
		if (node.getNodeType() == Node_base::ELEMENT_NODE) {
			statusInfoElem = Element<std::string>(node);
			if (statusInfoElem && boost::iequals(statusInfoElem.getLocalName(), "statusInfo"))
				break;
		}
		node = node.getNextSibling();
	}

	if (statusInfoElem && boost::iequals(statusInfoElem.getLocalName(), "statusInfo")) {
		node = statusInfoElem.getFirstChild();
		while (node) {
			if (node.getNodeType() == Node_base::TEXT_NODE) {
				msg.statusInfo = node.getNodeValue();
				break;
			}
			node = node.getNextSibling();
		}
	}
	return msg;
}


StatusRequest StatusRequest::fromXML(Arabica::DOM::Node<std::string> node, InterpreterImpl* interpreter) {
	StatusRequest msg(ContextualizedRequest::fromXML(node, interpreter));
	FIND_EVENT_NODE(node);

	Element<std::string> msgElem(node);
	std::string autoUpdate = STRING_ATTR_OR_EXPR(msgElem, RequestAutomaticUpdate);

	if (boost::iequals(autoUpdate, "true")) {
		msg.automaticUpdate = true;
	} else if(boost::iequals(autoUpdate, "on")) {
		msg.automaticUpdate = true;
	} else if(boost::iequals(autoUpdate, "yes")) {
		msg.automaticUpdate = true;
	} else if(boost::iequals(autoUpdate, "1")) {
		msg.automaticUpdate = true;
	} else {
		msg.automaticUpdate = false;
	}
	msg.type = STATUSREQUEST;
	return msg;
}



#ifdef MMI_WITH_OPERATOR_EVENT

TO_EVENT_OPERATOR(NewContextRequest,    "mmi.request.newcontext",    MMIEvent);
TO_EVENT_OPERATOR(PauseRequest,         "mmi.request.pause",         ContextualizedRequest);
TO_EVENT_OPERATOR(ResumeRequest,        "mmi.request.resume",        ContextualizedRequest);
TO_EVENT_OPERATOR(CancelRequest,        "mmi.request.cancel",        ContextualizedRequest);
TO_EVENT_OPERATOR(ClearContextRequest,  "mmi.request.clearcontext",  ContextualizedRequest);
TO_EVENT_OPERATOR(StatusRequest,        "mmi.request.status",        ContextualizedRequest);

TO_EVENT_OPERATOR(PrepareRequest,       "mmi.request.prepare",       ContentRequest);
TO_EVENT_OPERATOR(StartRequest,         "mmi.request.start",         ContentRequest);

TO_EVENT_OPERATOR(PrepareResponse,      "mmi.response.prepare",      StatusInfoResponse);
TO_EVENT_OPERATOR(StartResponse,        "mmi.response.start",        StatusInfoResponse);
TO_EVENT_OPERATOR(CancelResponse,       "mmi.response.cancel",       StatusInfoResponse);
TO_EVENT_OPERATOR(PauseResponse,        "mmi.response.pause",        StatusInfoResponse);
TO_EVENT_OPERATOR(ResumeResponse,       "mmi.response.resume",       StatusInfoResponse);
TO_EVENT_OPERATOR(ClearContextResponse, "mmi.response.clearcontext", StatusInfoResponse);
TO_EVENT_OPERATOR(NewContextResponse,   "mmi.response.newcontext",   StatusInfoResponse);
TO_EVENT_OPERATOR(DoneNotification,     "mmi.notification.done",     StatusInfoResponse);


MMIEvent::operator Event() const {
	Event ev;
	ev.setOriginType("mmi.event");
	ev.setOrigin(source);

	if (representation == MMI_AS_DATA) {
		if (dataDOM) {
			ev.data.node = dataDOM;
		} else {
			ev.data = Data::fromJSON(data);
			if (ev.data.empty()) {
				ev.content = data;
			}
		}
	}
	return ev;
}

ContextualizedRequest::operator Event() const {
	Event ev = MMIEvent::operator Event();
	// do we want to represent the context? It's the interpreters name already
	return ev;
}

ExtensionNotification::operator Event() const {
	Event ev = ContextualizedRequest::operator Event();
	if (name.length() > 0) {
		ev.setName(name);
	} else {
		ev.setName("mmi.notification.extension");
	}
	return ev;
}

ContentRequest::operator Event() const {
	Event ev = ContextualizedRequest::operator Event();
	if (representation == MMI_AS_DATA) {
		if (content.length() > 0)
			ev.data.compound["content"] = Data(content, Data::VERBATIM);
		if (contentURL.fetchTimeout.length() > 0)
			ev.data.compound["contentURL"].compound["fetchTimeout"] = Data(contentURL.fetchTimeout, Data::VERBATIM);
		if (contentURL.href.length() > 0)
			ev.data.compound["contentURL"].compound["href"] = Data(contentURL.href, Data::VERBATIM);
		if (contentURL.maxAge.length() > 0)
			ev.data.compound["contentURL"].compound["maxAge"] = Data(contentURL.maxAge, Data::VERBATIM);
	}
	return ev;
}

StatusResponse::operator Event() const {
	Event ev = ContextualizedRequest::operator Event();
	ev.setName("mmi.response.status");

	if (representation == MMI_AS_DATA) {
		switch (status) {
		case ALIVE:
			ev.data.compound["status"] = Data("alive", Data::VERBATIM);
			break;
		case DEAD:
			ev.data.compound["status"] = Data("dead", Data::VERBATIM);
			break;
		case SUCCESS:
			ev.data.compound["status"] = Data("success", Data::VERBATIM);
			break;
		case FAILURE:
			ev.data.compound["status"] = Data("failure", Data::VERBATIM);
			break;
		default:
			ev.data.compound["status"] = Data("invalid", Data::VERBATIM);
		}
	} else {
		ev.dom = toXML();
	}

	return ev;
}

#endif


}