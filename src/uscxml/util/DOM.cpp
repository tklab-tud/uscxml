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

#include <algorithm>

#include "uscxml/Common.h"
#include "uscxml/util/Convenience.h"
#include "uscxml/util/DOM.h"

#include <xercesc/util/PlatformUtils.hpp>
#include <xercesc/dom/DOM.hpp>
#include <xercesc/framework/StdOutFormatTarget.hpp>

#include "uscxml/interpreter/Logging.h"

namespace uscxml {

using namespace XERCESC_NS;

std::ostream& operator<< (std::ostream& os, const DOMNode& node) {

	DOMImplementation *implementation = DOMImplementationRegistry::getDOMImplementation(X("LS"));
	DOMLSSerializer *serializer = ((DOMImplementationLS*)implementation)->createLSSerializer();

	if (serializer->getDomConfig()->canSetParameter(XMLUni::fgDOMWRTFormatPrettyPrint, true))
		serializer->getDomConfig()->setParameter(XMLUni::fgDOMWRTFormatPrettyPrint, true);

	serializer->setNewLine(X("\r\n"));
	XMLCh* outString = serializer->writeToString(&node);
	os << X(outString);
	XMLString::release(&outString);

	delete (serializer);
	return os;
}

std::ostream& operator<< (std::ostream& os, const X& xmlString) {
	os << xmlString.str();
	return os;
}

std::string DOMUtils::idForNode(const DOMNode* node) {
	std::string nodeId;
	std::string seperator;
	const DOMNode* curr = node;
	while(curr) {
		switch (curr->getNodeType()) {
		case DOMNode::ELEMENT_NODE: {
			const DOMElement* elem = dynamic_cast<const DOMElement*>(curr);
			if (HAS_ATTR(elem, "id")) {
				std::string elementId = ATTR(elem, "id");
				std::replace( elementId.begin(), elementId.end(), '.', '_');
				std::replace( elementId.begin(), elementId.end(), ',', '_');

				nodeId.insert(0, elementId + seperator);
				seperator = "_";
				return nodeId;
			} else {
				DOMNode* sibling = curr->getPreviousSibling();
				int index = 0;
				while(sibling) {
					if (sibling->getNodeType() == DOMNode::ELEMENT_NODE) {
						if (iequals(TAGNAME_CAST(sibling), TAGNAME(elem))) {
							index++;
						}
					}
					sibling = sibling->getPreviousSibling();
				}
				nodeId.insert(0, TAGNAME(elem) + toStr(index) + seperator);
				seperator = "_";
			}
			break;
		}
		case DOMNode::DOCUMENT_NODE:
			return nodeId;
		default:
			break;
		}

		curr = curr->getParentNode();
	}
	return nodeId;
}

std::string DOMUtils::xPathForNode(const DOMNode* node, const std::string& ns) {
	std::string xPath;
	std::string nsPrefix;

	if (ns.size() > 0) {
		nsPrefix = ns + ":";
	}

	if (!node || node->getNodeType() != DOMNode::ELEMENT_NODE)
		return xPath;

	const DOMNode* curr = node;
	while(curr) {
		switch (curr->getNodeType()) {
		case DOMNode::ELEMENT_NODE: {
			const DOMElement* elem = dynamic_cast<const DOMElement*>(curr);
			if (HAS_ATTR(elem, "id")) {
				// we assume ids to be unique and return immediately
				if (ns == "*") {
					xPath.insert(0, "//*[local-name() = \"" + TAGNAME(elem) + "\"][@id=\"" + ATTR(elem, "id") + "\"]");
				} else {
					xPath.insert(0, "//" + nsPrefix + TAGNAME(elem) + "[@id=\"" + ATTR(elem, "id") + "\"]");
				}
				return xPath;
			} else {
				// check previous siblings to count our index
				DOMNode* sibling = curr->getPreviousSibling();
				int index = 1; // xpath indices start at 1
				while(sibling) {
					if (sibling->getNodeType() == DOMNode::ELEMENT_NODE) {
						if (iequals(TAGNAME_CAST(sibling), TAGNAME(elem))) {
							index++;
						}
					}
					sibling = sibling->getPreviousSibling();
				}
				if (ns == "*") {
					xPath.insert(0, "/*[local-name() = \"" + TAGNAME(elem) + "\"][" + toStr(index) + "]");
				} else {
					xPath.insert(0, "/" + nsPrefix + TAGNAME(elem) + "[" + toStr(index) + "]");
				}
			}
			break;
		}
		case DOMNode::DOCUMENT_NODE:
			return xPath;
		default:
			throw ErrorEvent("Only nodes of type element supported for now");
			return "";
			break;
		}
		curr = curr->getParentNode();
	}
	return xPath;
}

bool DOMUtils::hasIntersection(const std::list<DOMElement*>& l1, const std::list<DOMElement*>& l2) {
	for (auto i = l1.begin(); i != l1.end(); i++) {
		for (auto j = l2.begin(); j != l2.end(); j++) {
			if (*i == *j)
				return true;
		}
	}
	return false;
}

bool DOMUtils::isMember(const DOMNode* node,
                        const DOMNodeList* list) {
	for (size_t i = 0; i < list->getLength(); i++) {
		if (list->item(i) == node)
			return true;
	}
	return false;
}

bool DOMUtils::isMember(const DOMNode* node,
                        const std::list<DOMNode*>& list) {

	for (auto listIter = list.begin(); listIter != list.end(); listIter++) {
		if ((*listIter) == node)
			return true;
	}
	return false;
}

bool DOMUtils::isMember(const DOMElement* node,
                        const std::list<DOMElement*>& list) {

	for (auto listIter = list.begin(); listIter != list.end(); listIter++) {
		if ((*listIter) == node)
			return true;
	}
	return false;
}

const DOMElement* DOMUtils::getNearestAncestor(const DOMNode* node, const std::string tagName) {
	const DOMNode* parent = node->getParentNode();
	while(parent) {
		if (parent->getNodeType() == DOMNode::ELEMENT_NODE &&
		        iequals(TAGNAME_CAST(parent), tagName)) {
			return static_cast<const DOMElement*>(parent);
		}
		parent = parent->getParentNode();
	}
	return NULL;
}

bool DOMUtils::isDescendant(const DOMNode* s1,
                            const DOMNode* s2) {
	if (!s1 || !s2)
		return false;

	const DOMNode* parent = s1->getParentNode();
	while(parent) {
		if (s2 == parent)
			return true;
		parent = parent->getParentNode();
	}
	return false;
}

void DOMUtils::filterElementGeneric(const std::set<std::string>& elements,
                                    std::list<DOMElement*>& result,
                                    const DOMElement* root,
                                    const Order order,
                                    const bool includeEmbeddedDoc,
                                    const bool includeRoot) {

	if (!root)
		return;

	if ((order == NO_RECURSE || order == DOCUMENT) &&
	        includeRoot &&
	        elements.find(TAGNAME(root)) != elements.end()) {

		result.push_back((DOMElement*)root);
	}

	if (root->getNodeType() == DOMNode::ELEMENT_NODE && root->hasChildNodes()) {
		DOMElement* currElement = root->getFirstElementChild();
		while (currElement) {
			if (order == NO_RECURSE) {
				if (elements.find(TAGNAME(currElement)) != elements.end()) {
					result.push_back(currElement);
				}
			} else {
				if (includeEmbeddedDoc || TAGNAME(currElement) != XML_PREFIX(root).str() + "scxml") {
					filterElementGeneric(elements, result, currElement, order, includeEmbeddedDoc, true);
				}
			}
			currElement = currElement->getNextElementSibling();
		}
	}

	if (order == POSTFIX &&
	        includeRoot &&
	        elements.find(TAGNAME(root)) != elements.end()) {
		result.push_back((DOMElement*)root);
	}

}


void DOMUtils::filterTypeGeneric(const std::set<DOMNode::NodeType>& types,
                                 std::list<DOMNode*>& result,
                                 const DOMElement* root,
                                 const Order order,
                                 const bool includeEmbeddedDoc,
                                 const bool includeRoot) {

	if (!root)
		return;

	if ((order == NO_RECURSE || order == DOCUMENT) &&
	        includeRoot &&
	        types.find(root->getNodeType()) != types.end()) {
		result.push_back((DOMNode*)root);
	}

	if (root->getNodeType() == DOMNode::ELEMENT_NODE && root->hasChildNodes()) {
		DOMNode* currNode = root->getFirstChild();
		while (currNode) {
			if (currNode->getNodeType() != DOMNode::ELEMENT_NODE) {
				if (types.find(currNode->getNodeType()) != types.end()) {
					result.push_back(currNode);
				}
			} else {
				if (currNode->getNodeType() == DOMNode::ELEMENT_NODE) {
					DOMElement* currElement = (DOMElement*)currNode;
					if (includeEmbeddedDoc || TAGNAME(currElement) != XML_PREFIX(root).str() + "scxml") {
						filterTypeGeneric(types, result, currElement, order, includeEmbeddedDoc, true);
					}
				}
			}
			currNode = currNode->getNextSibling();
		}
	}

	if (order == POSTFIX &&
	        includeRoot &&
	        types.find(root->getNodeType()) != types.end()) {
		result.push_back((DOMNode*)root);
	}

}

#if 1
std::list<DOMElement*> DOMUtils::inPostFixOrder(const std::set<std::string>& elements,
        const DOMElement* root,
        const bool includeEmbeddedDoc) {
	std::list<DOMElement*> result;
	filterElementGeneric(elements, result, root, POSTFIX, includeEmbeddedDoc, true);
	return result;
}
#else
std::list<DOMElement*> DOMUtils::inPostFixOrder(const std::set<std::string>& elements,
        const DOMElement* root,
        const bool includeEmbeddedDoc) {
	std::list<DOMElement*> nodes;
	inPostFixOrder(elements, root, includeEmbeddedDoc, nodes);
	return nodes;
}
#endif

#if 1
std::list<DOMElement*> DOMUtils::inDocumentOrder(const std::set<std::string>& elements,
        const DOMElement* root,
        const bool includeEmbeddedDoc) {
	std::list<DOMElement*> result;
	filterElementGeneric(elements, result, root, DOCUMENT, includeEmbeddedDoc, true);
	return result;
}
#else
std::list<DOMElement*> DOMUtils::inDocumentOrder(const std::set<std::string>& elements,
        const DOMElement* root,
        const bool includeEmbeddedDoc) {
	std::list<DOMElement*> nodes;
	inDocumentOrder(elements, root, includeEmbeddedDoc, nodes);
	return nodes;
}
#endif

#if 1
std::list<DOMElement*> DOMUtils::filterChildElements(const std::string& tagName,
        const std::list<DOMElement*>& nodeSet,
        bool recurse) {

	std::list<DOMElement*> filteredChildElems;
	std::list<DOMElement*>::const_iterator nodeIter = nodeSet.begin();
	while(nodeIter != nodeSet.end()) {
		if ((*nodeIter)->getNodeType() == DOMNode::ELEMENT_NODE)
			filterElementGeneric({ tagName }, filteredChildElems, (DOMElement*)(*nodeIter), (recurse ? DOCUMENT : NO_RECURSE), true, false);
		nodeIter++;
	}
	return filteredChildElems;
}
#else
std::list<DOMElement*> DOMUtils::filterChildElements(const std::string& tagName,
        const std::list<DOMElement*>& nodeSet,
        bool recurse) {

	std::list<DOMElement*> filteredChildElems;
	std::list<DOMElement*>::const_iterator nodeIter = nodeSet.begin();
	while(nodeIter != nodeSet.end()) {
		std::list<DOMElement*> filtered = filterChildElements(tagName, *nodeIter, recurse);
		filteredChildElems.merge(filtered); // TODO: guess we want insert?
		nodeIter++;
	}
	return filteredChildElems;
}
#endif

#if 1
std::list<DOMElement*> DOMUtils::filterChildElements(const std::string& tagName,
        const DOMElement* node,
        bool recurse) {

	std::list<DOMElement*> result;
	filterElementGeneric({ tagName }, result, node, (recurse ? DOCUMENT : NO_RECURSE), true, false);
	return result;
}
#else
std::list<DOMElement*> DOMUtils::filterChildElements(const std::string& tagName,
        const DOMElement* node,
        bool recurse) {

	std::list<DOMElement*> filteredChildElems;

	if (!node)
		return filteredChildElems;

	for (auto childElem = node->getFirstElementChild(); childElem; childElem = childElem->getNextElementSibling()) {
		//		std::cerr << TAGNAME(childs.item(i)) << std::endl;
		if(iequals(TAGNAME(childElem), tagName)) {
			filteredChildElems.push_back((DOMElement*)childElem);
		}
		if (recurse) {
			std::list<DOMElement*> nested = filterChildElements(tagName, childElem, recurse);
			filteredChildElems.merge(nested);
		}
	}
	return filteredChildElems;
}

#endif

#if 1
std::list<DOMNode*> DOMUtils::filterChildType(const DOMNode::NodeType type,
        const std::list<DOMNode*>& nodeSet,
        bool recurse) {
	std::list<DOMNode*> filteredChildType;
	std::list<DOMNode*>::const_iterator nodeIter = nodeSet.begin();
	while(nodeIter != nodeSet.end()) {
		if ((*nodeIter)->getNodeType() == DOMNode::ELEMENT_NODE)
			filterTypeGeneric({ type }, filteredChildType, (DOMElement*)(*nodeIter), (recurse ? DOCUMENT : NO_RECURSE), true, false);
		nodeIter++;
	}
	return filteredChildType;
}
#else
std::list<DOMNode*> DOMUtils::filterChildType(const DOMNode::NodeType type,
        const std::list<DOMNode*>& nodeSet,
        bool recurse) {
	std::list<DOMNode*> filteredChildType;
	std::list<DOMNode*>::const_iterator nodeIter = nodeSet.begin();
	while(nodeIter != nodeSet.end()) {
		std::list<DOMNode*> filtered = filterChildType(type, *nodeIter, recurse);
		filteredChildType.merge(filtered);
		nodeIter++;
	}
	return filteredChildType;
}
#endif

#if 1
std::list<DOMNode*> DOMUtils::filterChildType(const DOMNode::NodeType type,
        const DOMNode* node,
        bool recurse) {

	std::list<DOMNode*> result;
	if (node) {
		assert(node->getNodeType() == DOMNode::ELEMENT_NODE);
	}
	filterTypeGeneric({ type }, result, (DOMElement*)node, (recurse ? DOCUMENT : NO_RECURSE), true, false);
	return result;
}
#else
std::list<DOMNode*> DOMUtils::filterChildType(const DOMNode::NodeType type,
        const DOMNode* node,
        bool recurse) {

	std::list<DOMNode*> filteredChildTypes;

	if (!node)
		return filteredChildTypes;

	for (auto child = node->getFirstChild(); child; child = child->getNextSibling()) {
		if (child->getNodeType() == type)
			filteredChildTypes.push_back(child);
		if (recurse) {
			std::list<DOMNode*> nested = filterChildType(type, child, recurse);
			filteredChildTypes.merge(nested);

		}
	}
	return filteredChildTypes;
}
#endif

#if 0
void DOMUtils::inPostFixOrder(const std::set<std::string>& elements,
                              const DOMElement* root,
                              const bool includeEmbeddedDoc,
                              std::list<DOMElement*>& nodes) {

	if (root == NULL)
		return;

	for (auto childElem = root->getFirstElementChild(); childElem; childElem = childElem->getNextElementSibling()) {
		if (!includeEmbeddedDoc && LOCALNAME(childElem) == "scxml")
			continue;
		inPostFixOrder(elements, childElem, includeEmbeddedDoc, nodes);

	}
	for (auto childElem = root->getFirstElementChild(); childElem; childElem = childElem->getNextElementSibling()) {
		if (!includeEmbeddedDoc && TAGNAME(childElem) == XML_PREFIX(root).str() + "scxml")
			continue;

		if (elements.find(TAGNAME(childElem)) != elements.end()) {
			nodes.push_back((DOMElement*)childElem);
		}
	}
}

void DOMUtils::inDocumentOrder(const std::set<std::string>& elements,
                               const DOMElement* root,
                               const bool includeEmbeddedDoc,
                               std::list<DOMElement*>& nodes) {
	if (root == NULL)
		return;

	if (elements.find(TAGNAME(root)) != elements.end()) {
		nodes.push_back((DOMElement*)root);
	}

	/// @todo: item from getChildNodes is O(N)!
	DOMElement* child = root->getFirstElementChild();
	while(child) {
		if (includeEmbeddedDoc || TAGNAME(child) != XML_PREFIX(root).str() + "scxml") {
			inDocumentOrder(elements, child, includeEmbeddedDoc, nodes);
		}

		child = child->getNextElementSibling();
	}
}
#endif
}
