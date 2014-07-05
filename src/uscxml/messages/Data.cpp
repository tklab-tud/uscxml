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

#include "uscxml/messages/Data.h"
#include "uscxml/messages/Blob.h"

#include <boost/algorithm/string.hpp>

#include "uscxml/DOMUtils.h"
#include "glog/logging.h"

#ifdef HAS_STRING_H
#include <string.h>
#endif

extern "C" {
#include "jsmn.h" // minimal json parser
}

namespace uscxml {

Data::Data(const char* data, size_t size, const std::string& mimeType, bool adopt) {
	binary = boost::shared_ptr<Blob>(new Blob(data, size, mimeType, adopt));
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
		Arabica::DOM::Element<std::string> payloadElem = document.createElementNS("http://www.w3.org/2005/07/scxml", "payload");
		payloadElem.setPrefix("scxml");

		scxmlMsg.appendChild(payloadElem);

		// we do not support nested attibutes
		if (compound.size() > 0) {
			std::map<std::string, Data>::iterator compoundIter = compound.begin();
			while(compoundIter != compound.end()) {
				if (compoundIter->second.atom.size() > 0) {
					Arabica::DOM::Element<std::string> propertyElem = document.createElementNS("http://www.w3.org/2005/07/scxml", "property");
					propertyElem.setPrefix("scxml");

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
				boost::replace_all(value, "\\n", "\n");
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

std::ostream& operator<< (std::ostream& os, const Data& data) {
	os << Data::toJSON(data);
	return os;
}

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
		// empty string is handled below
		if (data.type == Data::VERBATIM) {
			os << "\"";
			for (int i = 0; i < data.atom.size(); i++) {
				// escape string
				if (false) {
				} else if (data.atom[i] == '"') {
					os << "\\\"";
				} else if (data.atom[i] == '\n') {
					os << "\\n";
				} else if (data.atom[i] == '\t') {
					os << "\\t";
				} else {
					os << data.atom[i];
				}
			}
			os << "\"";
		} else {
			os << data.atom;
		}
	} else if (data.node) {
		std::ostringstream xmlSerSS;
		xmlSerSS << data.node;
		std::string xmlSer = xmlSerSS.str();
		boost::replace_all(xmlSer, "\"", "\\\"");
		boost::replace_all(xmlSer, "\n", "\\n");
		boost::replace_all(xmlSer, "\t", "\\t");
		os << "\"" << xmlSer << "\"";
	} else {
		if (data.type == Data::VERBATIM) {
			os << "\"\""; // empty string
		} else {
			os << "null";
		}
	}
	return os.str();
}

}