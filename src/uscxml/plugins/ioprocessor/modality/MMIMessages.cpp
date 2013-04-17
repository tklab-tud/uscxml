#include "MMIMessages.h"

#include <DOM/Simple/DOMImplementation.hpp>
#include <DOM/io/Stream.hpp>
#include <DOM/SAX2DOM/SAX2DOM.hpp>
#include <SAX/helpers/InputSourceResolver.hpp>

#include <boost/algorithm/string.hpp>

namespace uscxml {

using namespace Arabica::DOM;

std::string MMIMessage::nameSpace = "http://www.w3.org/2008/04/mmi-arch";

Arabica::DOM::Document<std::string> MMIMessage::toXML() {
	Arabica::DOM::DOMImplementation<std::string> domFactory = Arabica::SimpleDOM::DOMImplementation<std::string>::getDOMImplementation();
	Document<std::string> doc = domFactory.createDocument(nameSpace, "", 0);
	Element<std::string> mmiElem = doc.createElementNS(nameSpace, "mmi");
	Element<std::string> msgElem = doc.createElementNS(nameSpace, tagName);
	msgElem.setAttributeNS(nameSpace, "Source", source);
	msgElem.setAttributeNS(nameSpace, "Target", target);
	msgElem.setAttributeNS(nameSpace, "RequestID", requestId);

	if (data.size() > 0) {
		Element<std::string> dataElem = doc.createElementNS(nameSpace, "data");
		
		// try to parse content
		std::stringstream* ss = new std::stringstream();
		(*ss) << data;
		std::auto_ptr<std::istream> ssPtr(ss);
		Arabica::SAX::InputSource<std::string> inputSource;
		inputSource.setByteStream(ssPtr);
		
		Arabica::SAX2DOM::Parser<std::string> parser;
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
	std::cout << doc;
	return doc;
}

Arabica::DOM::Document<std::string> ContextualizedRequest::toXML() {
	Document<std::string> doc = MMIMessage::toXML();
	Element<std::string> msgElem = Element<std::string>(doc.getDocumentElement().getFirstChild());
	msgElem.setAttributeNS(nameSpace, "Context", context);
	return doc;
}

Arabica::DOM::Document<std::string> ContentRequest::toXML() {
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

Arabica::DOM::Document<std::string> ExtensionNotification::toXML() {
	Document<std::string> doc = ContextualizedRequest::toXML();
	Element<std::string> msgElem = Element<std::string>(doc.getDocumentElement().getFirstChild());
	msgElem.setAttributeNS(nameSpace, "Name", name);
	return doc;
}

Arabica::DOM::Document<std::string> StatusResponse::toXML() {
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

Arabica::DOM::Document<std::string> StatusInfoResponse::toXML() {
	Document<std::string> doc = StatusResponse::toXML();
	Element<std::string> msgElem = Element<std::string>(doc.getDocumentElement().getFirstChild());
	
	Element<std::string> statusInfoElem = doc.createElementNS(nameSpace, "StatusInfo");
	Text<std::string> statusInfoText = doc.createTextNode(statusInfo);
	statusInfoElem.appendChild(statusInfoText);
	msgElem.appendChild(statusInfoElem);
	
	return doc;
}

Arabica::DOM::Document<std::string> StatusRequest::toXML() {
	Document<std::string> doc = ContextualizedRequest::toXML();
	Element<std::string> msgElem = Element<std::string>(doc.getDocumentElement().getFirstChild());

	if (automaticUpdate) {
		msgElem.setAttributeNS(nameSpace, "RequestAutomaticUpdate", "true");
	} else {
		msgElem.setAttributeNS(nameSpace, "RequestAutomaticUpdate", "false");
	}
	
	return doc;
}

MMIMessage MMIMessage::fromXML(const Arabica::DOM::Document<std::string>& doc) {
	MMIMessage msg;
	Node<std::string> node = doc.getDocumentElement().getFirstChild();
	while (node) {
		if (node.getNodeType() == Node_base::ELEMENT_NODE)
			break;
		node = node.getNextSibling();
	}
	Element<std::string> msgElem(node);
	msg.source = msgElem.getAttributeNS("http://www.w3.org/2008/04/mmi-arch", "Source");
	msg.target = msgElem.getAttributeNS("http://www.w3.org/2008/04/mmi-arch", "Target");
//	msg.data = msgElem.getAttributeNS("http://www.w3.org/2008/04/mmi-arch", "Data");
	msg.requestId = msgElem.getAttributeNS("http://www.w3.org/2008/04/mmi-arch", "RequestID");
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
		while (node) {
			if (node.getNodeType() == Node_base::ELEMENT_NODE) {
				ss << node;
				break;
			}
			node = node.getNextSibling();
		}
		msg.data = ss.str();
	}
	
	return msg;
}

ContextualizedRequest ContextualizedRequest::fromXML(const Arabica::DOM::Document<std::string>& doc) {
	ContextualizedRequest msg(NewContextRequest::fromXML(doc));
	Node<std::string> node = doc.getDocumentElement().getFirstChild();
	while (node) {
		if (node.getNodeType() == Node_base::ELEMENT_NODE)
			break;
		node = node.getNextSibling();
	}
	Element<std::string> msgElem(node);
	msg.context = msgElem.getAttributeNS("http://www.w3.org/2008/04/mmi-arch", "Context");
	return msg;
}

ContentRequest ContentRequest::fromXML(const Arabica::DOM::Document<std::string>& doc) {
	ContentRequest msg(ContextualizedRequest::fromXML(doc));
	Node<std::string> node = doc.getDocumentElement().getFirstChild();
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
			msg.contentURL.href = contentElem.getAttributeNS("http://www.w3.org/2008/04/mmi-arch", "href");
			msg.contentURL.maxAge = contentElem.getAttributeNS("http://www.w3.org/2008/04/mmi-arch", "max-age");
			msg.contentURL.fetchTimeout = contentElem.getAttributeNS("http://www.w3.org/2008/04/mmi-arch", "fetchtimeout");
		}
	}
	
	//msg.content = msgElem.getAttributeNS("http://www.w3.org/2008/04/mmi-arch", "Context");
	return msg;
}

ExtensionNotification ExtensionNotification::fromXML(const Arabica::DOM::Document<std::string>& doc) {
	ExtensionNotification msg(ContextualizedRequest::fromXML(doc));
	Node<std::string> node = doc.getDocumentElement().getFirstChild();
	while (node) {
		if (node.getNodeType() == Node_base::ELEMENT_NODE)
			break;
		node = node.getNextSibling();
	}
	Element<std::string> msgElem(node);
	msg.name = msgElem.getAttributeNS("http://www.w3.org/2008/04/mmi-arch", "Name");
	return msg;
}

StatusResponse StatusResponse::fromXML(const Arabica::DOM::Document<std::string>& doc) {
	StatusResponse msg(ContextualizedRequest::fromXML(doc));
	Node<std::string> node = doc.getDocumentElement().getFirstChild();
	while (node) {
		if (node.getNodeType() == Node_base::ELEMENT_NODE)
			break;
		node = node.getNextSibling();
	}
	Element<std::string> msgElem(node);
	std::string status = msgElem.getAttributeNS("http://www.w3.org/2008/04/mmi-arch", "Status");

	if (boost::iequals(status, "ALIVE")) {
		msg.status = ALIVE;
	} else if(boost::iequals(status, "DEAD")) {
		msg.status = DEAD;
	} else if(boost::iequals(status, "FAILURE")) {
		msg.status = FAILURE;
	} else if(boost::iequals(status, "SUCCESS")) {
		msg.status = SUCCESS;
	}
	return msg;
}

StatusInfoResponse StatusInfoResponse::fromXML(const Arabica::DOM::Document<std::string>& doc) {
	StatusInfoResponse msg(StatusResponse::fromXML(doc));
	Node<std::string> node = doc.getDocumentElement().getFirstChild();
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

	
StatusRequest StatusRequest::fromXML(const Arabica::DOM::Document<std::string>& doc) {
	StatusRequest msg(ContextualizedRequest::fromXML(doc));
	Node<std::string> node = doc.getDocumentElement().getFirstChild();
	while (node) {
		if (node.getNodeType() == Node_base::ELEMENT_NODE)
			break;
		node = node.getNextSibling();
	}
	Element<std::string> msgElem(node);
	std::string autoUpdate = msgElem.getAttributeNS("http://www.w3.org/2008/04/mmi-arch", "RequestAutomaticUpdate");
	
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
	return msg;
}

}