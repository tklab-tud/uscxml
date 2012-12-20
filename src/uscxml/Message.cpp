#include "uscxml/Common.h"
#include "uscxml/Message.h"
//#include "uscxml/Interpreter.h"
#include <DOM/SAX2DOM/SAX2DOM.hpp>
#include <SAX/helpers/CatchErrorHandler.hpp>

namespace uscxml {

static int _dataIndentation = 1;

Data::Data(const Arabica::DOM::Node<std::string>& dom) {
	// we may need to convert some keys to arrays if we have the same name as an element
	std::map<std::string, std::list<Data> > arrays;
//  Interpreter::dump(dom);

	if (dom.hasAttributes()) {
		Arabica::DOM::NamedNodeMap<std::string> attributes = dom.getAttributes();
		for (int i = 0; i < attributes.getLength(); i++) {
			Arabica::DOM::Node<std::string> attribute = attributes.item(i);
//      Interpreter::dump(attribute);

			assert(attribute.getNodeType() == Arabica::DOM::Node_base::ATTRIBUTE_NODE);
			std::string key = attribute.getLocalName();
			std::string value = attribute.getNodeValue();
			compound[key] = Data(value, VERBATIM);
		}
	}

	if (dom.hasChildNodes()) {
		Arabica::DOM::NodeList<std::string> children = dom.getChildNodes();
		for (int i = 0; i < children.getLength(); i++) {
			Arabica::DOM::Node<std::string> child = children.item(i);
//      Interpreter::dump(child);
			std::string key;
			switch (child.getNodeType()) {
			case Arabica::DOM::Node_base::ELEMENT_NODE:
				key = TAGNAME(child);
				break;
			case Arabica::DOM::Node_base::ATTRIBUTE_NODE:
				key = ((Arabica::DOM::Attr<std::string>)child).getName();
				break;
			case Arabica::DOM::Node_base::TEXT_NODE:
			default:
				break;
			}
			if (key.length() == 0)
				continue;

			if (compound.find(key) != compound.end()) {
				// we already have such a key .. make it an array after we processed all children
				arrays[key].push_back(Data(child));
			} else {
				compound[key] = Data(child);
			}
		}
	} else {
		atom = dom.getNodeValue();
		type = VERBATIM;
	}

	std::map<std::string, std::list<Data> >::iterator arrayIter = arrays.begin();
	while(arrayIter != arrays.end()) {
		assert(compound.find(arrayIter->first) != compound.end());
		Data arrayData;
		arrays[arrayIter->first].push_front(compound[arrayIter->first]);
		arrayData.array = arrays[arrayIter->first];
		compound[arrayIter->first] = arrayData;
	}
}

Arabica::DOM::Document<std::string> Data::toDocument() {
	Arabica::DOM::DOMImplementation<std::string> domFactory = Arabica::SimpleDOM::DOMImplementation<std::string>::getDOMImplementation();
	Arabica::DOM::Document<std::string> document = domFactory.createDocument("http://www.w3.org/2005/07/scxml", "message", 0);
	Arabica::DOM::Element<std::string> scxmlMsg = document.getDocumentElement();
	scxmlMsg.setPrefix("scxml");
	scxmlMsg.setAttribute("version", "1.0");

	if (compound.size() > 0 || array.size() > 0) {
		Arabica::DOM::Element<std::string> payloadElem = document.createElementNS("http://www.w3.org/2005/07/scxml", "scxml:payload");
		scxmlMsg.appendChild(payloadElem);

		// we do not support nested attibutes
		if (compound.size() > 0) {
			std::map<std::string, Data>::iterator compoundIter = compound.begin();
			while(compoundIter != compound.end()) {
				if (compoundIter->second.atom.size() > 0) {
					Arabica::DOM::Element<std::string> propertyElem = document.createElementNS("http://www.w3.org/2005/07/scxml", "scxml:property");
					propertyElem.setAttribute("name", compoundIter->first);
					Arabica::DOM::Text<std::string> textElem = document.createTextNode(compoundIter->second.atom);
					propertyElem.appendChild(textElem);
					payloadElem.appendChild(propertyElem);
				}
				compoundIter++;
			}
		}
	}
	return document;
}

Arabica::DOM::Document<std::string> Event::toDocument() {
	Arabica::DOM::DOMImplementation<std::string> domFactory = Arabica::SimpleDOM::DOMImplementation<std::string>::getDOMImplementation();
	Arabica::DOM::Document<std::string> document = Data::toDocument();
	Arabica::DOM::Element<std::string> scxmlMsg = document.getDocumentElement();


	scxmlMsg.setAttribute("source", origin);
	scxmlMsg.setAttribute("name", name);

	return document;
}

Arabica::DOM::Document<std::string> SendRequest::toDocument() {
	Arabica::DOM::DOMImplementation<std::string> domFactory = Arabica::SimpleDOM::DOMImplementation<std::string>::getDOMImplementation();
	Arabica::DOM::Document<std::string> document = Event::toDocument();
	Arabica::DOM::Element<std::string> scxmlMsg = document.getDocumentElement();

	// add params and namelist
	if (params.size() > 0 || namelist.size() > 0) {
		Arabica::DOM::NodeList<std::string> payload = scxmlMsg.getElementsByTagName("scxml:payload");
		if (payload.getLength() == 0) {
			Arabica::DOM::Element<std::string> payloadElem = document.createElementNS("http://www.w3.org/2005/07/scxml", "scxml:payload");
			scxmlMsg.appendChild(payloadElem);
		}
		Arabica::DOM::Node<std::string> payloadElem = scxmlMsg.getElementsByTagName("scxml:payload").item(0);

		// add parameters
		std::multimap<std::string, std::string>::iterator paramIter = params.begin();
		while(paramIter != params.end()) {
			Arabica::DOM::Element<std::string> propertyElem = document.createElementNS("http://www.w3.org/2005/07/scxml", "scxml:property");
			propertyElem.setAttribute("name", paramIter->first);
			Arabica::DOM::Text<std::string> textElem = document.createTextNode(paramIter->second);
			propertyElem.appendChild(textElem);
			payloadElem.appendChild(propertyElem);
			paramIter++;
		}

		// add namelist elements
		std::map<std::string, std::string>::iterator namelistIter = namelist.begin();
		while(namelistIter != namelist.end()) {
			Arabica::DOM::Element<std::string> propertyElem = document.createElementNS("http://www.w3.org/2005/07/scxml", "scxml:property");
			propertyElem.setAttribute("name", namelistIter->first);
			Arabica::DOM::Text<std::string> textElem = document.createTextNode(namelistIter->second);
			propertyElem.appendChild(textElem);
			payloadElem.appendChild(propertyElem);
			namelistIter++;
		}

	}


	scxmlMsg.setAttribute("sendid", sendid);

	return document;
}

Arabica::DOM::Document<std::string> InvokeRequest::toDocument() {
	Arabica::DOM::DOMImplementation<std::string> domFactory = Arabica::SimpleDOM::DOMImplementation<std::string>::getDOMImplementation();
	Arabica::DOM::Document<std::string> document = Event::toDocument();
	Arabica::DOM::Element<std::string> scxmlMsg = document.getDocumentElement();

	scxmlMsg.setAttribute("invokeid", invokeid);

	return document;
}

Data Data::fromXML(const std::string& xmlString) {
	return Data();
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
							event.compound[key] = Data(value, VERBATIM);
						}
					}
				}
			}
		}
	}
	return event;
}

SendRequest SendRequest::fromXML(const std::string& xmlString) {
	Event::fromXML(xmlString);
	return SendRequest();
}

InvokeRequest InvokeRequest::fromXML(const std::string& xmlString) {
	Event::fromXML(xmlString);
	return InvokeRequest();
}

#ifndef SWIGJAVA
std::ostream& operator<< (std::ostream& os, const Event& event) {
	os << (event.type == Event::EXTERNAL ? "External" : "Internal") << " Event " /* << (event.dom ? "with DOM attached" : "")*/ << std::endl;

	if (event.name.size() > 0)
		os << "  name: " << event.name << std::endl;
	if (event.origin.size() > 0)
		os << "  origin: " << event.origin << std::endl;
	if (event.origintype.size() > 0)
		os << "  origintype: " << event.origintype << std::endl;
	_dataIndentation++;
	os << "  data: " << (Data)event << std::endl;
	_dataIndentation--;
	return os;
}
#endif

#ifndef SWIGJAVA
std::ostream& operator<< (std::ostream& os, const Data& data) {
	std::string indent;
	for (int i = 0; i < _dataIndentation; i++) {
		indent += "  ";
	}
	if (false) {
	} else if (data.compound.size() > 0) {
		int longestKey = 0;
		std::map<std::string, Data>::const_iterator compoundIter = data.compound.begin();
		while(compoundIter != data.compound.end()) {
			if (compoundIter->first.size() > longestKey)
				longestKey = compoundIter->first.size();
			compoundIter++;
		}
		std::string keyPadding;
		for (unsigned int i = 0; i < longestKey; i++)
			keyPadding += " ";

		os << "{" << std::endl;
		compoundIter = data.compound.begin();
		while(compoundIter != data.compound.end()) {
			os << indent << "  \"" << compoundIter->first << "\" " << keyPadding.substr(0, longestKey - compoundIter->first.size()) << ": ";
			_dataIndentation += 2;
			os << compoundIter->second << "," << std::endl;
			_dataIndentation -= 2;
			compoundIter++;
		}
		os << indent << "}" << std::endl;
	} else if (data.array.size() > 0) {
		os << "[" << std::endl;
		std::map<std::string, Data>::const_iterator compoundIter = data.compound.begin();
		while(compoundIter != data.compound.end()) {
			_dataIndentation += 2;
			os << indent << "  " << compoundIter->second << "," << std::endl;
			_dataIndentation -= 2;
			compoundIter++;
		}
		os << indent << "]" << std::endl;
	} else if (data.atom.size() > 0) {
		if (data.type == Data::VERBATIM) {
			os << indent << "\"" << data.atom << "\"";
		} else {
			os << indent << data.atom;
		}
	}
	return os;
}
#endif

}