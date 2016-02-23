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

#include "uscxml/Common.h"
#include "uscxml/UUID.h"
#include "uscxml/dom/DOMUtils.h"
#include "uscxml/Convenience.h"

#include <glog/logging.h>
#include <boost/algorithm/string.hpp>

namespace uscxml {

using namespace Arabica::XPath;
using namespace Arabica::DOM;

bool DOMUtils::attributeIsTrue(const::std::string& value) {
	return stringIsTrue(value.c_str());
}

std::string DOMUtils::idForNode(const Arabica::DOM::Node<std::string>& node) {
	std::string nodeId;
	std::string seperator;
	Arabica::DOM::Node<std::string> curr = node;
	while(curr) {
		switch (curr.getNodeType()) {
		case Arabica::DOM::Node_base::ELEMENT_NODE: {
			Arabica::DOM::Element<std::string> elem = Arabica::DOM::Element<std::string>(curr);
			if (HAS_ATTR(elem, "id") && !UUID::isUUID(ATTR(elem, "id"))) {
				std::string elementId = ATTR(elem, "id");
				boost::replace_all(elementId, ".", "_");
				boost::replace_all(elementId, ",", "_");
				nodeId.insert(0, elementId + seperator);
				seperator = "_";
				return nodeId;
			} else {
				Arabica::DOM::Node<std::string> sibling = curr.getPreviousSibling();
				int index = 0;
				while(sibling) {
					if (sibling.getNodeType() == Arabica::DOM::Node_base::ELEMENT_NODE) {
						if (iequals(TAGNAME_CAST(sibling), TAGNAME(elem))) {
							index++;
						}
					}
					sibling = sibling.getPreviousSibling();
				}
				nodeId.insert(0, TAGNAME(elem) + toStr(index) + seperator);
				seperator = "_";
			}
			break;
		}
		case Arabica::DOM::Node_base::DOCUMENT_NODE:
			return nodeId;
		}

		curr = curr.getParentNode();
	}
	return nodeId;
}

std::string DOMUtils::xPathForNode(const Arabica::DOM::Node<std::string>& node, const std::string& ns) {
	std::string xPath;
	std::string nsPrefix;

	if (ns.size() > 0) {
		nsPrefix = ns + ":";
	}

	if (!node || node.getNodeType() != Arabica::DOM::Node_base::ELEMENT_NODE)
		return xPath;

	Arabica::DOM::Node<std::string> curr = node;
	while(curr) {
		switch (curr.getNodeType()) {
		case Arabica::DOM::Node_base::ELEMENT_NODE: {
			Arabica::DOM::Element<std::string> elem = Arabica::DOM::Element<std::string>(curr);
			if (HAS_ATTR(elem, "id") && !UUID::isUUID(ATTR(elem, "id"))) {
				// we assume ids to be unique and return immediately
				if (ns == "*") {
					xPath.insert(0, "//*[local-name() = \"" + TAGNAME(elem) + "\"][@id=\"" + ATTR(elem, "id") + "\"]");
				} else {
					xPath.insert(0, "//" + nsPrefix + TAGNAME(elem) + "[@id=\"" + ATTR(elem, "id") + "\"]");
				}
				return xPath;
			} else {
				// check previous siblings to count our index
				Arabica::DOM::Node<std::string> sibling = curr.getPreviousSibling();
				int index = 1; // xpath indices start at 1
				while(sibling) {
					if (sibling.getNodeType() == Arabica::DOM::Node_base::ELEMENT_NODE) {
						if (iequals(TAGNAME_CAST(sibling), TAGNAME(elem))) {
							index++;
						}
					}
					sibling = sibling.getPreviousSibling();
				}
				if (ns == "*") {
					xPath.insert(0, "/*[local-name() = \"" + TAGNAME(elem) + "\"][" + toStr(index) + "]");
				} else {
					xPath.insert(0, "/" + nsPrefix + TAGNAME(elem) + "[" + toStr(index) + "]");
				}
			}
			break;
		}
		case Arabica::DOM::Node_base::DOCUMENT_NODE:
			return xPath;
		default:
			LOG(ERROR) << "Only nodes of type element supported for now";
			return "";
			break;
		}
		curr = curr.getParentNode();
	}
	return xPath;
}

NodeSet<std::string> DOMUtils::inPostFixOrder(const std::set<std::string>& elements,
        const Element<std::string>& root,
        const bool includeEmbeddedDoc) {
	NodeSet<std::string> nodes;
	inPostFixOrder(elements, root, includeEmbeddedDoc, nodes);
	return nodes;
}

void DOMUtils::inPostFixOrder(const std::set<std::string>& elements,
                              const Element<std::string>& root,
                              const bool includeEmbeddedDoc,
                              NodeSet<std::string>& nodes) {
	NodeList<std::string> children = root.getChildNodes();
	for (size_t i = 0; i < children.getLength(); i++) {
		if (children.item(i).getNodeType() != Node_base::ELEMENT_NODE)
			continue;
		Arabica::DOM::Element<std::string> childElem(children.item(i));
		if (!includeEmbeddedDoc && LOCALNAME(childElem) == "scxml")
			continue;
		inPostFixOrder(elements, childElem, includeEmbeddedDoc, nodes);

	}
	for (size_t i = 0; i < children.getLength(); i++) {
		if (children.item(i).getNodeType() != Node_base::ELEMENT_NODE)
			continue;
		Arabica::DOM::Element<std::string> childElem(children.item(i));
		if (!includeEmbeddedDoc && LOCALNAME(childElem) == "scxml")
			continue;

		if (elements.find(TAGNAME(childElem)) != elements.end()) {
			nodes.push_back(childElem);
		}
	}
}

NodeSet<std::string> DOMUtils::inDocumentOrder(const std::set<std::string>& elements,
        const Element<std::string>& root,
        const bool includeEmbeddedDoc) {
	NodeSet<std::string> nodes;
	inDocumentOrder(elements, root, includeEmbeddedDoc, nodes);
	return nodes;
}

void DOMUtils::inDocumentOrder(const std::set<std::string>& elements,
                               const Element<std::string>& root,
                               const bool includeEmbeddedDoc,
                               NodeSet<std::string>& nodes) {
	if (elements.find(TAGNAME(root)) != elements.end()) {
		nodes.push_back(root);
	}

	NodeList<std::string> children = root.getChildNodes();
	for (size_t i = 0; i < children.getLength(); i++) {
		if (children.item(i).getNodeType() != Node_base::ELEMENT_NODE)
			continue;
		if (!includeEmbeddedDoc && LOCALNAME_CAST(children.item(i)) == "scxml")
			continue;
		Arabica::DOM::Element<std::string> childElem(children.item(i));
		inDocumentOrder(elements, childElem, includeEmbeddedDoc, nodes);
	}
}

std::list<Arabica::DOM::Node<std::string> > DOMUtils::getElementsByType(const Arabica::DOM::Node<std::string>& root, Arabica::DOM::Node_base::Type type) {
	std::list<Arabica::DOM::Node<std::string> > result;
	std::list<Arabica::DOM::Node<std::string> > stack;
	std::list<Arabica::DOM::Node<std::string> >::iterator stackIter;

	if (!root)
		return result;

	stack.push_back(root);
	while(stack.size() > 0) {
//		for(stackIter = stack.begin(); stackIter != stack.end(); stackIter++) {
//			std::cout << stackIter->getNodeType() << " " << stackIter->getLocalName() << " " << stackIter->getNodeValue() << std::endl;
//		}
//		std::cout << std::endl;

		Arabica::DOM::Node<std::string> currNode = stack.back();
		if (currNode.hasChildNodes()) {
			stack.push_back(currNode.getFirstChild());
			continue;
		}

		// roll back stack and pop everyone without next sibling
		do {
			currNode = stack.back();
			if (currNode.getNodeType() == type)
				result.push_back(currNode);
			stack.pop_back();
			if (currNode.getNextSibling()) {
				stack.push_back(currNode.getNextSibling());
				break;
			}
		} while(stack.size() > 0);
	}
	return result;
}


NodeSet<std::string> DOMUtils::filterChildElements(const std::string& tagName, const NodeSet<std::string>& nodeSet, bool recurse) {
	NodeSet<std::string> filteredChildElems;
	for (unsigned int i = 0; i < nodeSet.size(); i++) {
		filteredChildElems.push_back(filterChildElements(tagName, nodeSet[i], recurse));
	}
	return filteredChildElems;
}

NodeSet<std::string> DOMUtils::filterChildElements(const std::string& tagName, const Node<std::string>& node, bool recurse) {
	NodeSet<std::string> filteredChildElems;

	if (!node)
		return filteredChildElems;

	NodeList<std::string> childs = node.getChildNodes();
	for (unsigned int i = 0; i < childs.getLength(); i++) {
		if (childs.item(i).getNodeType() != Node_base::ELEMENT_NODE)
			continue;
		//		std::cerr << TAGNAME(childs.item(i)) << std::endl;
		if(iequals(TAGNAME_CAST(childs.item(i)), tagName)) {
			filteredChildElems.push_back(childs.item(i));
		}
		if (recurse) {
			filteredChildElems.push_back(filterChildElements(tagName, childs.item(i), recurse));
		}
	}
	return filteredChildElems;
}


NodeSet<std::string> DOMUtils::filterChildType(const Node_base::Type type, const NodeSet<std::string>& nodeSet, bool recurse) {
	NodeSet<std::string> filteredChildType;
	for (unsigned int i = 0; i < nodeSet.size(); i++) {
		filteredChildType.push_back(filterChildType(type, nodeSet[i], recurse));
	}
	return filteredChildType;
}

NodeSet<std::string> DOMUtils::filterChildType(const Node_base::Type type, const Node<std::string>& node, bool recurse) {
	NodeSet<std::string> filteredChildTypes;

	if (!node)
		return filteredChildTypes;

	NodeList<std::string> childs = node.getChildNodes();
	for (unsigned int i = 0; i < childs.getLength(); i++) {
		if (childs.item(i).getNodeType() == type)
			filteredChildTypes.push_back(childs.item(i));
		if (recurse) {
			filteredChildTypes.push_back(filterChildType(type, childs.item(i), recurse));
		}
	}
	return filteredChildTypes;
}


}