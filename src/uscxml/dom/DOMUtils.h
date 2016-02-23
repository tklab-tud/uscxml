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
#include <vector>
#include <iostream>
#include <DOM/Document.hpp>
#include <DOM/io/Stream.hpp> // operator<< for nodes
#include <XPath/XPath.hpp>

#define TAGNAME_CAST(elem) ((Arabica::DOM::Element<std::string>)elem).getTagName()
#define LOCALNAME_CAST(elem) ((Arabica::DOM::Element<std::string>)elem).getLocalName()
#define ATTR_CAST(elem, attr) ((Arabica::DOM::Element<std::string>)elem).getAttribute(attr)
#define ATTR_NODE_CAST(elem, attr) ((Arabica::DOM::Element<std::string>)elem).getAttributeNode(attr)
#define HAS_ATTR_CAST(elem, attr) ((Arabica::DOM::Element<std::string>)elem).hasAttribute(attr)

#define TAGNAME(elem) elem.getTagName()
#define LOCALNAME(elem) elem.getLocalName()
#define ATTR(elem, attr) elem.getAttribute(attr)
#define ATTR_NODE(elem, attr) elem.getAttributeNode(attr)
#define HAS_ATTR(elem, attr) elem.hasAttribute(attr)

namespace uscxml {

class USCXML_API DOMUtils {
public:

	static std::string xPathForNode(const Arabica::DOM::Node<std::string>& node, const std::string& ns = "");
	static std::list<Arabica::DOM::Node<std::string> > getElementsByType(const Arabica::DOM::Node<std::string>& root, Arabica::DOM::Node_base::Type type);
	static std::string idForNode(const Arabica::DOM::Node<std::string>& node);
	// deprecated, use stringIsTrue from Convenience.h instead
	DEPRECATED static bool attributeIsTrue(const::std::string& value);

	static Arabica::XPath::NodeSet<std::string> inPostFixOrder(const std::string& element,
	        const Arabica::DOM::Element<std::string>& root,
	        const bool includeEmbeddedDoc = false) {
		std::set<std::string> elements;
		elements.insert(element);
		return inPostFixOrder(elements, root, includeEmbeddedDoc);
	}

	static Arabica::XPath::NodeSet<std::string> inPostFixOrder(const std::set<std::string>& elements,
	        const Arabica::DOM::Element<std::string>& root,
	        const bool includeEmbeddedDoc = false);

	static Arabica::XPath::NodeSet<std::string> inDocumentOrder(const std::string& element,
	        const Arabica::DOM::Element<std::string>& root,
	        const bool includeEmbeddedDoc = false) {
		std::set<std::string> elements;
		elements.insert(element);
		return inDocumentOrder(elements, root, includeEmbeddedDoc);
	}

	static Arabica::XPath::NodeSet<std::string> inDocumentOrder(const std::set<std::string>& elements,
	        const Arabica::DOM::Element<std::string>& root,
	        const bool includeEmbeddedDoc = false);

	static Arabica::XPath::NodeSet<std::string> filterChildElements(const std::string& tagname,
	        const Arabica::DOM::Node<std::string>& node,
	        bool recurse = false);

	static Arabica::XPath::NodeSet<std::string> filterChildElements(const std::string& tagName,
	        const Arabica::XPath::NodeSet<std::string>& nodeSet,
	        bool recurse = false);

	static Arabica::XPath::NodeSet<std::string> filterChildType(const Arabica::DOM::Node_base::Type type,
	        const Arabica::DOM::Node<std::string>& node,
	        bool recurse = false);

	static Arabica::XPath::NodeSet<std::string> filterChildType(const Arabica::DOM::Node_base::Type type,
	        const Arabica::XPath::NodeSet<std::string>& nodeSet,
	        bool recurse = false);

protected:
	static void inPostFixOrder(const std::set<std::string>& elements,
	                           const Arabica::DOM::Element<std::string>& root,
	                           const bool includeEmbeddedDoc,
	                           Arabica::XPath::NodeSet<std::string>& nodes);

	static void inDocumentOrder(const std::set<std::string>& elements,
	                            const Arabica::DOM::Element<std::string>& root,
	                            const bool includeEmbeddedDoc,
	                            Arabica::XPath::NodeSet<std::string>& nodes);


};


}


#endif /* end of include guard: DOMUTILS_H_WK0WAEA7 */
