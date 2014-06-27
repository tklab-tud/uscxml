/**
 *  @file
 *  @author     2012-2014 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#include "uscxml/messages/SendRequest.h"
#include <DOM/Simple/DOMImplementation.hpp>
#include <DOM/Document.hpp>
#include <DOM/io/Stream.hpp>

namespace uscxml {

std::string SendRequest::toXMLString() {
	std::stringstream ss;
	ss << toDocument();
	return ss.str();
}

Arabica::DOM::Document<std::string> SendRequest::toDocument() {
	Arabica::DOM::DOMImplementation<std::string> domFactory = Arabica::SimpleDOM::DOMImplementation<std::string>::getDOMImplementation();
	Arabica::DOM::Document<std::string> document = Event::toDocument();
	Arabica::DOM::Element<std::string> scxmlMsg = document.getDocumentElement();

	// add params and namelist
	if (params.size() > 0 || namelist.size() > 0) {
		Arabica::DOM::NodeList<std::string> payload = scxmlMsg.getElementsByTagName("scxml:payload");
		if (payload.getLength() == 0) {
			Arabica::DOM::Element<std::string> payloadElem = document.createElementNS("http://www.w3.org/2005/07/scxml", "payload");
			payloadElem.setPrefix("scxml");

			scxmlMsg.appendChild(payloadElem);
		}
		Arabica::DOM::Node<std::string> payloadElem = scxmlMsg.getElementsByTagName("scxml:payload").item(0);

		// add parameters
		std::multimap<std::string, Data>::iterator paramIter = params.begin();
		while(paramIter != params.end()) {
			Arabica::DOM::Element<std::string> propertyElem = document.createElementNS("http://www.w3.org/2005/07/scxml", "property");
			propertyElem.setPrefix("scxml");

			propertyElem.setAttribute("name", paramIter->first);
			// this is simplified - Data might be more elaborate than a simple string atom
			Arabica::DOM::Text<std::string> textElem = document.createTextNode(paramIter->second.atom);
			propertyElem.appendChild(textElem);
			payloadElem.appendChild(propertyElem);
			paramIter++;
		}

		// add namelist elements
		std::map<std::string, Data>::iterator namelistIter = namelist.begin();
		while(namelistIter != namelist.end()) {
			Arabica::DOM::Element<std::string> propertyElem = document.createElementNS("http://www.w3.org/2005/07/scxml", "property");
			propertyElem.setPrefix("scxml");

			propertyElem.setAttribute("name", namelistIter->first);
			// this is simplified - Data might be more elaborate than a simple string atom
			Arabica::DOM::Text<std::string> textElem = document.createTextNode(namelistIter->second.atom);
			propertyElem.appendChild(textElem);
			payloadElem.appendChild(propertyElem);
			namelistIter++;
		}

	}

	scxmlMsg.setAttribute("sendid", sendid);

	return document;
}

SendRequest SendRequest::fromXML(const std::string& xmlString) {
	Event::fromXML(xmlString);
	return SendRequest();
}

std::ostream& operator<< (std::ostream& os, const SendRequest& sendReq) {

	std::string indent;
	for (int i = 0; i < _dataIndentation; i++) {
		indent += "  ";
	}

	os << indent << "SendReq" << std::endl;

	if (sendReq.target.size() > 0)
		os << indent << "  target: " << sendReq.target << std::endl;

	if (sendReq.type.size() > 0)
		os << indent << "  type: " << sendReq.type << std::endl;

	if (sendReq.delayMs > 0)
		os<< indent  << "  delay: " << sendReq.delayMs << std::endl;

	if (sendReq.namelist.size() > 0) {
		os << indent << "  namelist: " << std::endl;
		SendRequest::namelist_t::const_iterator namelistIter = sendReq.namelist.begin();
		while(namelistIter != sendReq.namelist.end()) {
			os << indent << "    " << namelistIter->first << ": " << namelistIter->second << std::endl;
			namelistIter++;
		}
	}

	if (sendReq.params.size() > 0) {
		os << indent << "  params: " << std::endl;
		SendRequest::params_t::const_iterator paramIter = sendReq.params.begin();
		while(paramIter != sendReq.params.end()) {
			os << indent << "    " << paramIter->first << ": " << paramIter->second << std::endl;
			paramIter++;
		}
	}

	if (sendReq.content.size() > 0)
		os << indent << "  content: " << sendReq.content << std::endl;

	_dataIndentation++;
	os << (Event)sendReq;
	_dataIndentation--;
	return os;

}

}