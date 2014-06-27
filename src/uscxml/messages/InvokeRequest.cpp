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

#include "uscxml/messages/InvokeRequest.h"
#include <DOM/Simple/DOMImplementation.hpp>
#include <DOM/Document.hpp>
#include <DOM/io/Stream.hpp>

namespace uscxml {

std::string InvokeRequest::toXMLString() {
	std::stringstream ss;
	ss << toDocument();
	return ss.str();
}

Arabica::DOM::Document<std::string> InvokeRequest::toDocument() {
	Arabica::DOM::DOMImplementation<std::string> domFactory = Arabica::SimpleDOM::DOMImplementation<std::string>::getDOMImplementation();
	Arabica::DOM::Document<std::string> document = Event::toDocument();
	Arabica::DOM::Element<std::string> scxmlMsg = document.getDocumentElement();

	scxmlMsg.setAttribute("invokeid", invokeid);

	return document;
}

InvokeRequest InvokeRequest::fromXML(const std::string& xmlString) {
	Event::fromXML(xmlString);
	return InvokeRequest();
}

std::ostream& operator<< (std::ostream& os, const InvokeRequest& invokeReq) {

	std::string indent;
	for (int i = 0; i < _dataIndentation; i++) {
		indent += "  ";
	}

	os << indent << "InvokeReq" << (invokeReq.autoForward ? " with autoforward" : "") << std::endl;

	if (invokeReq.type.size() > 0)
		os << indent << "  type: " << invokeReq.type << std::endl;

	if (invokeReq.src.size() > 0)
		os<< indent  << "  src: " << invokeReq.src << std::endl;

	if (invokeReq.namelist.size() > 0) {
		os << indent << "  namelist: " << std::endl;
		InvokeRequest::namelist_t::const_iterator namelistIter = invokeReq.namelist.begin();
		while(namelistIter != invokeReq.namelist.end()) {
			os << indent << "    " << namelistIter->first << ": " << namelistIter->second << std::endl;
			namelistIter++;
		}
	}

	if (invokeReq.params.size() > 0) {
		os << indent << "  params: " << std::endl;
		InvokeRequest::params_t::const_iterator paramIter = invokeReq.params.begin();
		while(paramIter != invokeReq.params.end()) {
			os << indent << "    " << paramIter->first << ": " << paramIter->second << std::endl;
			paramIter++;
		}
	}

	if (invokeReq.content.size() > 0)
		os << indent << "  content: " << invokeReq.content << std::endl;

	_dataIndentation++;
	os << (Event)invokeReq;
	_dataIndentation--;
	return os;

}

}