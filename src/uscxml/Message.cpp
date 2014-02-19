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

#include "uscxml/config.h"

#include "uscxml/Common.h"
#include "uscxml/Message.h"
#include "uscxml/DOMUtils.h"
#include <DOM/SAX2DOM/SAX2DOM.hpp>
#include <SAX/helpers/CatchErrorHandler.hpp>
#include <glog/logging.h>

#include <boost/algorithm/string.hpp>

#ifdef HAS_STRING_H
#include <string.h>
#endif

extern "C" {
#include "jsmn.h" // minimal json parser
}

namespace uscxml {

static int _dataIndentation = 1;

Blob::~Blob() {
	free(data);
}

Blob::Blob(size_t _size) {
	data = (char*)malloc(_size);
	memset(data, 0, _size);
	size = _size;
}

Blob::Blob(void* _data, size_t _size, const std::string& _mimeType, bool adopt) {
	if (adopt) {
		data = (char*)_data;
	} else {
		data = (char*)malloc(_size);
		memcpy(data, _data, _size);
	}
	mimeType = _mimeType;
	size = _size;
}

#if 0
// this used to work base64 encoded images in a browser - can't check extensively just now
static const std::string base64_chars =
    "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
    "abcdefghijklmnopqrstuvwxyz"
    "0123456789+/";

std::string Blob::base64() {

	int in_len = size;
	char const* bytes_to_encode = data;

	std::string ret;
	int i = 0;
	int j = 0;
	unsigned char char_array_3[3];
	unsigned char char_array_4[4];

	while (in_len--) {
		char_array_3[i++] = *(bytes_to_encode++);
		if (i == 3) {
			char_array_4[0] = (char_array_3[0] & 0xfc) >> 2;
			char_array_4[1] = ((char_array_3[0] & 0x03) << 4) + ((char_array_3[1] & 0xf0) >> 4);
			char_array_4[2] = ((char_array_3[1] & 0x0f) << 2) + ((char_array_3[2] & 0xc0) >> 6);
			char_array_4[3] = char_array_3[2] & 0x3f;

			for(i = 0; (i <4) ; i++)
				ret += base64_chars[char_array_4[i]];
			i = 0;
		}
	}

	if (i) {
		for(j = i; j < 3; j++)
			char_array_3[j] = '\0';

		char_array_4[0] = (char_array_3[0] & 0xfc) >> 2;
		char_array_4[1] = ((char_array_3[0] & 0x03) << 4) + ((char_array_3[1] & 0xf0) >> 4);
		char_array_4[2] = ((char_array_3[1] & 0x0f) << 2) + ((char_array_3[2] & 0xc0) >> 6);
		char_array_4[3] = char_array_3[2] & 0x3f;

		for (j = 0; (j < i + 1); j++)
			ret += base64_chars[char_array_4[j]];

		while((i++ < 3))
			ret += '=';

	}

	return ret;

}
#else
std::string Blob::base64() {
	return base64Encode((char* const)data, size);
}
#endif

Data::Data(const char* _data, size_t _size, const std::string& mimeType, bool adopt) {
	binary = boost::shared_ptr<Blob>(new Blob((void*)_data, _size, mimeType, adopt));
}

void Data::merge(const Data& other) {
	if (other.compound.size() > 0) {
		if (compound.size() == 0) {
			compound = other.compound;
		} else {
			std::map<std::string, Data>::const_iterator compIter = other.compound.begin();
			while (compIter !=  other.compound.end()) {
				if (compound.find(compIter->first) != compound.end()) {
					// we do have the same key, merge
					compound[compIter->first].merge(compIter->second);
				} else {
					compound[compIter->first] = compIter->second;
				}
				compIter++;
			}
		}
	}
	if (other.array.size() > 0) {
		if (array.size() == 0) {
			array = other.array;
		} else {
			std::list<Data>::const_iterator arrIter = other.array.begin();
			while(arrIter != other.array.end()) {
				array.push_back(*arrIter);
				arrIter++;
			}
		}
	}
	if (other.atom.size() > 0) {
		atom = other.atom;
		type = other.type;
	}
}

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

Arabica::DOM::Document<std::string> Event::toDocument() {
	Arabica::DOM::DOMImplementation<std::string> domFactory = Arabica::SimpleDOM::DOMImplementation<std::string>::getDOMImplementation();
	Arabica::DOM::Document<std::string> document = data.toDocument();
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
		std::multimap<std::string, Data>::iterator paramIter = params.begin();
		while(paramIter != params.end()) {
			Arabica::DOM::Element<std::string> propertyElem = document.createElementNS("http://www.w3.org/2005/07/scxml", "scxml:property");
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
			Arabica::DOM::Element<std::string> propertyElem = document.createElementNS("http://www.w3.org/2005/07/scxml", "scxml:property");
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

Data Data::fromJSON(const std::string& jsonString) {
	Data data;

	std::string trimmed = boost::trim_copy(jsonString);

	if (trimmed.length() == 0)
		return data;

	if (trimmed.find_first_of("{[") != 0)
		return data;

	jsmn_parser p;

	jsmntok_t* t = NULL;

	// we do not know the number of tokens beforehand, start with something sensible and increase
	int rv;
	int frac = 16; // length/token ratio
	do {
		jsmn_init(&p);

		frac /= 2;
		int nrTokens = trimmed.size() / frac;
		if (t != NULL) {
			free(t);
//      LOG(INFO) << "Increasing JSON length to token ratio to 1/" << frac;
		}
		t = (jsmntok_t*)malloc((nrTokens + 1) * sizeof(jsmntok_t));
		if (t == NULL) {
			LOG(ERROR) << "Cannot parse JSON, ran out of memory!";
			return data;
		}
		memset(t, 0, (nrTokens + 1) * sizeof(jsmntok_t));

		rv = jsmn_parse(&p, trimmed.c_str(), t, nrTokens);
	} while (rv == JSMN_ERROR_NOMEM && frac > 1);

	if (rv != 0) {
		switch (rv) {
		case JSMN_ERROR_NOMEM:
			LOG(ERROR) << "Cannot parse JSON, not enough tokens were provided!";
			break;
		case JSMN_ERROR_INVAL:
			LOG(ERROR) << "Cannot parse JSON, invalid character inside JSON string!";
			break;
		case JSMN_ERROR_PART:
			LOG(ERROR) << "Cannot parse JSON, the string is not a full JSON packet, more bytes expected!";
			break;
		default:
			break;
		}
		free(t);
		return data;
	}

	if (t[0].end != trimmed.length())
		return data;

//	jsmntok_t* token = t;
//	while(token->end) {
//		std::cout << trimmed.substr(token->start, token->end - token->start) << std::endl;
//		std::cout << "------" << std::endl;
//		token++;
//	}

	std::list<Data*> dataStack;
	std::list<jsmntok_t> tokenStack;
	dataStack.push_back(&data);

	size_t currTok = 0;
	do {
		// used for debugging
//		jsmntok_t t2 = t[currTok];
//		std::string value = trimmed.substr(t[currTok].start, t[currTok].end - t[currTok].start);
		switch (t[currTok].type) {
		case JSMN_STRING:
			dataStack.back()->type = Data::VERBATIM;
		case JSMN_PRIMITIVE: {
			std::string value = trimmed.substr(t[currTok].start, t[currTok].end - t[currTok].start);
			if (dataStack.back()->type == Data::VERBATIM) {
				boost::replace_all(value, "\\\"", "\"");
			}
			dataStack.back()->atom = value;
			dataStack.pop_back();
			currTok++;
			break;
		}
		case JSMN_OBJECT:
		case JSMN_ARRAY:
			tokenStack.push_back(t[currTok]);
			currTok++;
			break;
		}
		// used for debugging
//		t2 = t[currTok];
//		value = trimmed.substr(t[currTok].start, t[currTok].end - t[currTok].start);

		// there are no more tokens
		if (t[currTok].end == 0 || tokenStack.empty())
			break;

		// next token starts after current one => pop
		while (t[currTok].end > tokenStack.back().end) {
			tokenStack.pop_back();
			dataStack.pop_back();
		}

		if (tokenStack.back().type == JSMN_OBJECT && (t[currTok].type == JSMN_PRIMITIVE || t[currTok].type == JSMN_STRING)) {
			// grab key and push new data
			std::string value = trimmed.substr(t[currTok].start, t[currTok].end - t[currTok].start);
			dataStack.push_back(&(dataStack.back()->compound[value]));
			currTok++;
		}
		if (tokenStack.back().type == JSMN_ARRAY) {
			// push new index
			dataStack.back()->array.push_back(Data());
			dataStack.push_back(&(dataStack.back()->array.back()));
		}

	} while (true);

	free(t);
	return data;
}

void Event::initContent(const std::string& content) {
	// try to parse as JSON
	Data json = Data::fromJSON(content);
	if (json) {
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

SendRequest SendRequest::fromXML(const std::string& xmlString) {
	Event::fromXML(xmlString);
	return SendRequest();
}

InvokeRequest InvokeRequest::fromXML(const std::string& xmlString) {
	Event::fromXML(xmlString);
	return InvokeRequest();
}

#ifndef SWIGJAVA
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
		SendRequest::params_t::const_iterator paramIter = invokeReq.params.begin();
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
#endif


#ifndef SWIGJAVA
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
#endif

#ifndef SWIGJAVA
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
	_dataIndentation++;
	os << indent << "  data: " << event.data << std::endl;
	_dataIndentation--;
	return os;
}
#endif

#ifndef SWIGJAVA
std::ostream& operator<< (std::ostream& os, const Data& data) {
	os << Data::toJSON(data);
	return os;
}
#endif

std::string Data::toJSON(const Data& data) {
	std::stringstream os;
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

		std::string seperator;
		os << std::endl << indent << "{";
		compoundIter = data.compound.begin();
		while(compoundIter != data.compound.end()) {
			os << seperator << std::endl << indent << "  \"" << compoundIter->first << "\": " << keyPadding.substr(0, longestKey - compoundIter->first.size());
			_dataIndentation += 1;
			os << compoundIter->second;
			_dataIndentation -= 1;
			seperator = ", ";
			compoundIter++;
		}
		os << std::endl << indent << "}";
	} else if (data.array.size() > 0) {

		std::string seperator;
		os << std::endl << indent << "[";
		std::list<Data>::const_iterator arrayIter = data.array.begin();
		while(arrayIter != data.array.end()) {
			_dataIndentation += 1;
			os << seperator << *arrayIter;
			_dataIndentation -= 1;
			seperator = ", ";
			arrayIter++;
		}
		os << "]";
	} else if (data.atom.size() > 0) {
		if (data.type == Data::VERBATIM) {
			os << "\"";
			for (int i = 0; i < data.atom.size(); i++) {
				// escape string
				if (data.atom[i] == '"') {
					os << '\\';
				}
				os << data.atom[i];
			}
			os << "\"";
		} else {
			os << data.atom;
		}
	} else if (data.node) {
		if (data.type == Data::VERBATIM) {
			os << "";
		} else {
			os << data.atom;
		}
	} else {
		os << "undefined";
	}
	return os.str();
}

}