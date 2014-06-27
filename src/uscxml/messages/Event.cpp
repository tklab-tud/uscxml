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

#include "uscxml/messages/Event.h"
#include "uscxml/DOMUtils.h"

namespace uscxml {

//Arabica::DOM::Node<std::string> Event::getFirstDOMElement() const {
//	return getFirstDOMElement(dom);
//}
//
//Arabica::DOM::Document<std::string> Event::getStrippedDOM() const {
//	return getStrippedDOM(dom);
//}

//Arabica::DOM::Node<std::string> Event::getFirstDOMElement(const Arabica::DOM::Document<std::string> dom) {
//	Arabica::DOM::Node<std::string> data = dom.getDocumentElement().getFirstChild();
//	while (data) {
//		if (data.getNodeType() == Arabica::DOM::Node_base::TEXT_NODE) {
//			std::string trimmed = boost::trim_copy(data.getNodeValue());
//			if (trimmed.length() == 0) {
//				data = data.getNextSibling();
//				continue;
//			}
//		}
//		break;
//	}
//	return data;
//}
//
//Arabica::DOM::Document<std::string> Event::getStrippedDOM(const Arabica::DOM::Document<std::string> dom) {
//	Arabica::DOM::DOMImplementation<std::string> domFactory = Arabica::SimpleDOM::DOMImplementation<std::string>::getDOMImplementation();
//	Arabica::DOM::Document<std::string> document = domFactory.createDocument("", "", 0);
//	if (dom) {
//		document.getDocumentElement().appendChild(document.importNode(getFirstDOMElement(dom), true));
//	}
//	return document;
//}

std::string Event::toXMLString() {
	std::stringstream ss;
	ss << toDocument();
	return ss.str();
}

Arabica::DOM::Document<std::string> Event::toDocument() {
	Arabica::DOM::DOMImplementation<std::string> domFactory = Arabica::SimpleDOM::DOMImplementation<std::string>::getDOMImplementation();
	Arabica::DOM::Document<std::string> document = data.toDocument();
	Arabica::DOM::Element<std::string> scxmlMsg = document.getDocumentElement();


	scxmlMsg.setAttribute("source", origin);
	scxmlMsg.setAttribute("name", name);

	return document;
}

void Event::initContent(const std::string& content) {
	// try to parse as JSON
	Data json = Data::fromJSON(content);
	if (!json.empty()) {
		data = json;
		return;
	}

	// try to parse as XML
	Arabica::SAX2DOM::Parser<std::string> parser;
	Arabica::SAX::CatchErrorHandler<std::string> errorHandler;
	parser.setErrorHandler(errorHandler);

	std::istringstream is(content);
	Arabica::SAX::InputSource<std::string> inputSource;
	inputSource.setByteStream(is);
	if (parser.parse(inputSource)) {
		dom = parser.getDocument();
		return;
	}

	this->content = content;
}

Event Event::fromXML(const std::string& xmlString) {
	Arabica::SAX2DOM::Parser<std::string> eventParser;
	Arabica::SAX::CatchErrorHandler<std::string> errorHandler;
	eventParser.setErrorHandler(errorHandler);

	std::istringstream is(xmlString);
	Arabica::SAX::InputSource<std::string> inputSource;
	inputSource.setByteStream(is);

	Event event;
	if(eventParser.parse(inputSource) && eventParser.getDocument().hasChildNodes()) {
		Arabica::DOM::Element<std::string> scxmlMsg = eventParser.getDocument().getDocumentElement();
		if (HAS_ATTR(scxmlMsg, "name"))
			event.name = ATTR(scxmlMsg, "name");
		if (HAS_ATTR(scxmlMsg, "sendid"))
			event.sendid = ATTR(scxmlMsg, "sendid");

		Arabica::DOM::NodeList<std::string> payloads = scxmlMsg.getElementsByTagName("scxml:payload");
		if (payloads.getLength() > 0) {
			Arabica::DOM::Node<std::string> payload = payloads.item(0);
			if (payload.getNodeType() == Arabica::DOM::Node_base::ELEMENT_NODE) {
				Arabica::DOM::Element<std::string> payloadElem = (Arabica::DOM::Element<std::string>)payload;
				Arabica::DOM::NodeList<std::string> properties = payloadElem.getElementsByTagName("scxml:property");
				if (properties.getLength() > 0) {
					for (int i = 0; i < properties.getLength(); i++) {
						if (HAS_ATTR(properties.item(i), "name")) {
							std::string key = ATTR(properties.item(i), "name");
							std::string value;
							Arabica::DOM::NodeList<std::string> childs = properties.item(i).getChildNodes();
							for (int j = 0; j < childs.getLength(); j++) {
								if (childs.item(j).getNodeType() == Arabica::DOM::Node_base::TEXT_NODE) {
									value = childs.item(j).getNodeValue();
									break;
								}
							}
							event.data.compound[key] = Data(value, Data::VERBATIM);
						}
					}
				}
			}
		}
	}
	return event;
}

std::ostream& operator<< (std::ostream& os, const Event& event) {
	std::string indent;
	for (int i = 0; i < _dataIndentation; i++) {
		indent += "  ";
	}

	os << indent << (event.eventType == Event::EXTERNAL ? "External" : "Internal") << " Event " << (event.dom ? "with DOM attached" : "") << std::endl;

	if (event.name.size() > 0)
		os << indent << "  name: " << event.name << std::endl;
	if (event.origin.size() > 0)
		os << indent << "  origin: " << event.origin << std::endl;
	if (event.origintype.size() > 0)
		os << indent << "  origintype: " << event.origintype << std::endl;
	if (event.params.size() > 0) {
		std::multimap<std::string, Data>::const_iterator paramIter = event.params.begin();
		os << indent << "  params:" << std::endl;
		_dataIndentation++;
		while(paramIter != event.params.end()) {
			os << indent << "    " << paramIter->first << ": ";
			os << indent << paramIter->second << std::endl;
			paramIter++;
		}
		_dataIndentation--;
	}
	if (event.namelist.size() > 0) {
		std::map<std::string, Data>::const_iterator namelistIter = event.namelist.begin();
		os << indent << "  namelist:" << std::endl;
		_dataIndentation++;
		while(namelistIter != event.namelist.end()) {
			os << indent << "    " << namelistIter->first << ": ";
			os << indent << namelistIter->second << std::endl;
			namelistIter++;
		}
		_dataIndentation--;

	}
	_dataIndentation++;
	os << indent << "  data: " << event.data << std::endl;
	_dataIndentation--;
	return os;
}

}