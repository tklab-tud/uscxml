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

#include "MMIMessages.h"

#include <DOM/Simple/DOMImplementation.hpp>
#include <DOM/io/Stream.hpp>
#include <DOM/SAX2DOM/SAX2DOM.hpp>
#include <SAX/helpers/InputSourceResolver.hpp>

#include <uscxml/NameSpacingParser.h>

#include <boost/algorithm/string.hpp>

#define STRING_ATTR_OR_EXPR(element, name)\
(element.hasAttributeNS(nameSpace, "name##Expr") && interpreter ? \
	interpreter->getDataModel().evalAsString(element.getAttributeNS(nameSpace, "name##Expr")) : \
	(element.hasAttributeNS(nameSpace, #name) ? element.getAttributeNS(nameSpace, #name) : "") \
)


namespace uscxml {

using namespace Arabica::DOM;

std::string MMIEvent::nameSpace = "http://www.w3.org/2008/04/mmi-arch";

MMIEvent::Type MMIEvent::getType(Arabica::DOM::Node<std::string> node) {
	if (!node)
		return INVALID;

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

Arabica::DOM::Node<std::string> MMIEvent::getEventNode(Arabica::DOM::Node<std::string> node) {
	if (!node)
		return node;

	if (node.getNodeType() == Node_base::DOCUMENT_NODE)
		node = Arabica::DOM::Document<std::string>(node).getDocumentElement();

	// get the first element
	while (node && node.getNodeType() != Node_base::ELEMENT_NODE) {
		node = node.getNextSibling();
	}
	// get the contained message
	if (node && getType(node) == INVALID) {
		node = node.getFirstChild();
		while (node && node.getNodeType() != Node_base::ELEMENT_NODE && getType(node) == INVALID) {
			node = node.getNextSibling();
		}
	}
	return node;
}


Arabica::DOM::Document<std::string> MMIEvent::toXML() const {
	Arabica::DOM::DOMImplementation<std::string> domFactory = Arabica::SimpleDOM::DOMImplementation<std::string>::getDOMImplementation();
	Document<std::string> doc = domFactory.createDocument(nameSpace, "", 0);
	Element<std::string> mmiElem = doc.createElementNS(nameSpace, "mmi");
	Element<std::string> msgElem = doc.createElementNS(nameSpace, tagName);
	msgElem.setAttributeNS(nameSpace, "Source", source);
	msgElem.setAttributeNS(nameSpace, "Target", target);
	msgElem.setAttributeNS(nameSpace, "RequestID", requestId);

	if (data.size() > 0) {
		Element<std::string> dataElem = doc.createElementNS(nameSpace, "Data");

		// try to parse content
		std::stringstream* ss = new std::stringstream();
		(*ss) << data;
		std::auto_ptr<std::istream> ssPtr(ss);
		Arabica::SAX::InputSource<std::string> inputSource;
		inputSource.setByteStream(ssPtr);

		NameSpacingParser parser;
		if(parser.parse(inputSource)) {
			Node<std::string> importedNode = doc.importNode(parser.getDocument().getDocumentElement(), true);
			dataElem.appendChild(importedNode);
		} else {
			Text<std::string> textElem = doc.createTextNode(data);
			dataElem.appendChild(textElem);
		}
		msgElem.appendChild(dataElem);
	}

	mmiElem.appendChild(msgElem);
	doc.appendChild(mmiElem);
	return doc;
}

Arabica::DOM::Document<std::string> ContextualizedRequest::toXML() const {
	Document<std::string> doc = MMIEvent::toXML();
	Element<std::string> msgElem = Element<std::string>(doc.getDocumentElement().getFirstChild());
	msgElem.setAttributeNS(nameSpace, "Context", context);
	return doc;
}

Arabica::DOM::Document<std::string> ContentRequest::toXML() const {
	Document<std::string> doc = ContextualizedRequest::toXML();
	Element<std::string> msgElem = Element<std::string>(doc.getDocumentElement().getFirstChild());

	if (contentURL.href.size() > 0) {
		Element<std::string> contentURLElem = doc.createElementNS(nameSpace, "contentURL");
		contentURLElem.setAttributeNS(nameSpace, "href", contentURL.href);
		contentURLElem.setAttributeNS(nameSpace, "fetchtimeout", contentURL.fetchTimeout);
		contentURLElem.setAttributeNS(nameSpace, "max-age", contentURL.maxAge);
		msgElem.appendChild(contentURLElem);
	}

	if (content.size() > 0) {
		Element<std::string> contentElem = doc.createElementNS(nameSpace, "content");

		// try to parse content
		std::stringstream* ss = new std::stringstream();
		(*ss) << content;
		std::auto_ptr<std::istream> ssPtr(ss);
		Arabica::SAX::InputSource<std::string> inputSource;
		inputSource.setByteStream(ssPtr);

		Arabica::SAX2DOM::Parser<std::string> parser;
		if(parser.parse(inputSource)) {
			Node<std::string> importedNode = doc.importNode(parser.getDocument().getDocumentElement(), true);
			contentElem.appendChild(importedNode);
		} else {
			Text<std::string> textElem = doc.createTextNode(content);
			contentElem.appendChild(textElem);
		}
		msgElem.appendChild(contentElem);

	}
	return doc;
}

Arabica::DOM::Document<std::string> ExtensionNotification::toXML() const {
	Document<std::string> doc = ContextualizedRequest::toXML();
	Element<std::string> msgElem = Element<std::string>(doc.getDocumentElement().getFirstChild());
	msgElem.setAttributeNS(nameSpace, "Name", name);
	return doc;
}

Arabica::DOM::Document<std::string> StatusResponse::toXML() const {
	Document<std::string> doc = ContextualizedRequest::toXML();
	Element<std::string> msgElem = Element<std::string>(doc.getDocumentElement().getFirstChild());
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

Arabica::DOM::Document<std::string> StatusInfoResponse::toXML() const {
	Document<std::string> doc = StatusResponse::toXML();
	Element<std::string> msgElem = Element<std::string>(doc.getDocumentElement().getFirstChild());

	Element<std::string> statusInfoElem = doc.createElementNS(nameSpace, "StatusInfo");
	Text<std::string> statusInfoText = doc.createTextNode(statusInfo);
	statusInfoElem.appendChild(statusInfoText);
	msgElem.appendChild(statusInfoElem);

	return doc;
}

Arabica::DOM::Document<std::string> StatusRequest::toXML() const {
	Document<std::string> doc = ContextualizedRequest::toXML();
	Element<std::string> msgElem = Element<std::string>(doc.getDocumentElement().getFirstChild());

	if (automaticUpdate) {
		msgElem.setAttributeNS(nameSpace, "RequestAutomaticUpdate", "true");
	} else {
		msgElem.setAttributeNS(nameSpace, "RequestAutomaticUpdate", "false");
	}

	return doc;
}

MMIEvent MMIEvent::fromXML(Arabica::DOM::Node<std::string> node, InterpreterImpl* interpreter) {
	MMIEvent msg;
	while (node) {
		if (node.getNodeType() == Node_base::ELEMENT_NODE)
			break;
		node = node.getNextSibling();
	}
	Element<std::string> msgElem(node);
	msg.source = STRING_ATTR_OR_EXPR(msgElem, Source);
	msg.target = STRING_ATTR_OR_EXPR(msgElem, Target);
//	msg.data = STRING_ATTR_OR_EXPR(msgElem, Data);
	msg.requestId = STRING_ATTR_OR_EXPR(msgElem, RequestID);
	msg.tagName = msgElem.getLocalName();

	Element<std::string> dataElem;
	node = msgElem.getFirstChild();
	while (node) {
		if (node.getNodeType() == Node_base::ELEMENT_NODE)
			dataElem = Element<std::string>(node);
		if (dataElem && boost::iequals(dataElem.getLocalName(), "data"))
			break;
		node = node.getNextSibling();
	}

	if (dataElem && boost::iequals(dataElem.getLocalName(), "data")) {
		std::stringstream ss;
		node = dataElem.getFirstChild();
		if (node)
			ss << node;
		msg.data = ss.str();
	}

	return msg;
}

MMIEvent::operator Event() const {
	Event ev;
	ev.setOriginType("mmi.event");
	ev.setOrigin(source);
	ev.setRaw(data);
	ev.setSendId(requestId);
	if (data.length() > 0) {
		ev.initContent(data);
	}
	return ev;
}

ContextualizedRequest ContextualizedRequest::fromXML(Arabica::DOM::Node<std::string> node, InterpreterImpl* interpreter) {
	ContextualizedRequest msg(MMIEvent::fromXML(node, interpreter));
	while (node) {
		if (node.getNodeType() == Node_base::ELEMENT_NODE)
			break;
		node = node.getNextSibling();
	}
	Element<std::string> msgElem(node);
	msg.context = STRING_ATTR_OR_EXPR(msgElem, Context);
	return msg;
}

ContextualizedRequest::operator Event() const {
	Event ev = MMIEvent::operator Event();
	// do we want to represent the context? It's the interpreters name already
	return ev;
}


ContentRequest ContentRequest::fromXML(Arabica::DOM::Node<std::string> node, InterpreterImpl* interpreter) {
	ContentRequest msg(ContextualizedRequest::fromXML(node, interpreter));
	while (node) {
		if (node.getNodeType() == Node_base::ELEMENT_NODE)
			break;
		node = node.getNextSibling();
	}
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
			std::stringstream ss;
			node = contentElem.getFirstChild();
			while (node) {
				if (node.getNodeType() == Node_base::ELEMENT_NODE) {
					ss << node;
					break;
				}
				node = node.getNextSibling();
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

ExtensionNotification ExtensionNotification::fromXML(Arabica::DOM::Node<std::string> node, InterpreterImpl* interpreter) {
	ExtensionNotification msg(ContextualizedRequest::fromXML(node, interpreter));
	while (node) {
		if (node.getNodeType() == Node_base::ELEMENT_NODE)
			break;
		node = node.getNextSibling();
	}
	Element<std::string> msgElem(node);
	msg.name = STRING_ATTR_OR_EXPR(msgElem, Name);
	msg.type = EXTENSIONNOTIFICATION;
	return msg;
}

ExtensionNotification::operator Event() const {
	Event ev = ContextualizedRequest::operator Event();
	if (name.length() > 0) {
		ev.setName("mmi.extensionnotification." + name);
	} else {
		ev.setName("mmi.extensionnotification");
	}
	return ev;
}

StatusResponse StatusResponse::fromXML(Arabica::DOM::Node<std::string> node, InterpreterImpl* interpreter) {
	StatusResponse msg(ContextualizedRequest::fromXML(node, interpreter));
	while (node) {
		if (node.getNodeType() == Node_base::ELEMENT_NODE)
			break;
		node = node.getNextSibling();
	}
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
	}
	msg.type = STATUSRESPONSE;
	return msg;
}

StatusInfoResponse StatusInfoResponse::fromXML(Arabica::DOM::Node<std::string> node, InterpreterImpl* interpreter) {
	StatusInfoResponse msg(StatusResponse::fromXML(node, interpreter));
	while (node) {
		if (node.getNodeType() == Node_base::ELEMENT_NODE)
			break;
		node = node.getNextSibling();
	}
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
	while (node) {
		if (node.getNodeType() == Node_base::ELEMENT_NODE)
			break;
		node = node.getNextSibling();
	}
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


}