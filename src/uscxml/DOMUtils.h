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

#ifndef DOMUTILS_H_WK0WAEA7
#define DOMUTILS_H_WK0WAEA7

#include "uscxml/Common.h"
#include <DOM/SAX2DOM/SAX2DOM.hpp>
#include <SAX/helpers/DefaultHandler.hpp>
#include <SAX/helpers/CatchErrorHandler.hpp>
#include <DOM/io/Stream.hpp> // operator<< for nodes

#define TAGNAME(elem) ((Arabica::DOM::Element<std::string>)elem).getTagName()
#define LOCALNAME(elem) ((Arabica::DOM::Element<std::string>)elem).getLocalName()
#define ATTR(elem, attr) ((Arabica::DOM::Element<std::string>)elem).getAttribute(attr)
#define ATTR_NODE(elem, attr) ((Arabica::DOM::Element<std::string>)elem).getAttributeNode(attr)
#define HAS_ATTR(elem, attr) ((Arabica::DOM::Element<std::string>)elem).hasAttribute(attr)

namespace uscxml {

class USCXML_API DOMUtils {
public:
	static std::string xPathForNode(const Arabica::DOM::Node<std::string>& node, const std::string& ns = "");
	static std::list<Arabica::DOM::Node<std::string> > getElementsByType(const Arabica::DOM::Node<std::string>& root, Arabica::DOM::Node_base::Type type);
	static bool attributeIsTrue(const::std::string& value);
};

class USCXML_API NumAttr {
public:
	NumAttr(const std::string& str) {
		size_t valueStart = str.find_first_of("0123456789.");
		if (valueStart != std::string::npos) {
			size_t valueEnd = str.find_last_of("0123456789.");
			if (valueEnd != std::string::npos) {
				value = str.substr(valueStart, (valueEnd - valueStart) + 1);
				size_t unitStart = str.find_first_not_of(" \t", valueEnd + 1);
				if (unitStart != std::string::npos) {
					size_t unitEnd = str.find_last_of(" \t");
					if (unitEnd != std::string::npos && unitEnd > unitStart) {
						unit = str.substr(unitStart, unitEnd - unitStart);
					} else {
						unit = str.substr(unitStart, str.length() - unitStart);
					}
				}
			}
		}
	}

	std::string value;
	std::string unit;
};

class ScriptEntityResolver : public Arabica::SAX::EntityResolver<std::string> {
	virtual InputSourceT resolveEntity(const std::string& publicId, const std::string& systemId) {
		Arabica::SAX::InputSource<std::string> is;
		return is;
	}
};

class USCXML_API NameSpacingParser : public Arabica::SAX2DOM::Parser<std::string> {
public:
	NameSpacingParser();
	NameSpacingParser(const NameSpacingParser& other) {}
	static NameSpacingParser fromXML(const std::string& xml);
	static NameSpacingParser fromInputSource(Arabica::SAX::InputSource<std::string>& source);

	void startPrefixMapping(const std::string& prefix, const std::string& uri);

	std::map<std::string, std::string> nameSpace;

	virtual bool errorsReported() {
		return _errorHandler.errorsReported();
	}

	virtual const std::string& errors() {
		return _errorHandler.errors();
	}

private:
	Arabica::SAX::CatchErrorHandler<std::string> _errorHandler;
};

}


#endif /* end of include guard: DOMUTILS_H_WK0WAEA7 */
