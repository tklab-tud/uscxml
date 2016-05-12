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

#include <set>
#include <list>
#include <iostream>

#include "uscxml/Common.h"
#include <xercesc/util/XMLString.hpp>
#include <xercesc/dom/DOM.hpp>


/*
#define TAGNAME_CAST(elem) ((Arabica::DOM::Element<std::string>)elem).getTagName()
#define LOCALNAME_CAST(elem) ((Arabica::DOM::Element<std::string>)elem).getLocalName()
#define ATTR_CAST(elem, attr) ((Arabica::DOM::Element<std::string>)elem).getAttribute(attr)
#define ATTR_NODE_CAST(elem, attr) ((Arabica::DOM::Element<std::string>)elem).getAttributeNode(attr)
#define HAS_ATTR_CAST(elem, attr) ((Arabica::DOM::Element<std::string>)elem).hasAttribute(attr)

#define TAGNAME(elem) elem.getTagName()
#define LOCALNAME(elem) elem.getLocalName()
#define ATTR(elem, attr) elem.getAttribute(attr)
#define ATTR_NODE(elem, attr) elem.getAttributeNode(attr)
*/

#define HAS_ATTR(elem, attr) (elem)->hasAttribute(X(attr))
#define HAS_ATTR_CAST(elem, attr) HAS_ATTR(static_cast<const DOMElement*>(elem), attr)
#define ATTR(elem, attr) std::string(X((elem)->getAttribute(X(attr))))
#define ATTR_CAST(elem, attr) ATTR(static_cast<const DOMElement*>(elem), attr)
#define TAGNAME(elem) std::string(X((elem)->getTagName()))
#define TAGNAME_CAST(elem) TAGNAME(static_cast<const DOMElement*>(elem))
#define LOCALNAME(elem) std::string(X((elem)->getLocalName()))
#define LOCALNAME_CAST(elem) LOCALNAME(static_cast<const DOMElement*>(elem))



namespace uscxml {

class USCXML_API DOMUtils {
public:

	static const xercesc::DOMNode* getNearestAncestor(const xercesc::DOMNode* node, const std::string tagName);
	static bool isDescendant(const xercesc::DOMNode* s1, const xercesc::DOMNode* s2);


	static bool hasIntersection(const std::list<xercesc::DOMElement*>& l1,
	                            const std::list<xercesc::DOMElement*>& l2);
	static bool isMember(const xercesc::DOMElement* node, const std::list<xercesc::DOMElement*>& list);
	static bool isMember(const xercesc::DOMNode* node, const std::list<xercesc::DOMNode*>& list);
	static bool isMember(const xercesc::DOMNode* node, const xercesc::DOMNodeList* list);

	static std::string xPathForNode(const xercesc::DOMNode* node,
	                                const std::string& ns = "");
	static std::string idForNode(const xercesc::DOMNode* node);

	static std::list<xercesc::DOMNode*> getElementsByType(const xercesc::DOMNode* root,
	        xercesc::DOMNode::NodeType type);

	static std::list<xercesc::DOMElement*> inPostFixOrder(const std::string& element,
	        const xercesc::DOMElement* root,
	        const bool includeEmbeddedDoc = false) {
		std::set<std::string> elements;
		elements.insert(element);
		return inPostFixOrder(elements, root, includeEmbeddedDoc);
	}

	static std::list<xercesc::DOMElement*> inPostFixOrder(const std::set<std::string>& elements,
	        const xercesc::DOMElement* root,
	        const bool includeEmbeddedDoc = false);


	static std::list<xercesc::DOMElement*> inDocumentOrder(const std::string& element,
	        const xercesc::DOMElement* root,
	        const bool includeEmbeddedDoc = false) {
		std::set<std::string> elements;
		elements.insert(element);
		return inDocumentOrder(elements, root, includeEmbeddedDoc);
	}

	static std::list<xercesc::DOMElement*> inDocumentOrder(const std::set<std::string>& elements,
	        const xercesc::DOMElement* root,
	        const bool includeEmbeddedDoc = false);

	static std::list<xercesc::DOMElement*> filterChildElements(const std::string& tagName,
	        const xercesc::DOMElement* node,
	        bool recurse = false);

	static std::list<xercesc::DOMElement*> filterChildElements(const std::string& tagName,
	        const std::list<xercesc::DOMElement*>& nodeSet,
	        bool recurse = false);

	static std::list<xercesc::DOMNode*> filterChildType(const xercesc::DOMNode::NodeType type,
	        const xercesc::DOMNode* node,
	        bool recurse = false);

	static std::list<xercesc::DOMNode*> filterChildType(const xercesc::DOMNode::NodeType type,
	        const std::list<xercesc::DOMNode*>& nodeSet,
	        bool recurse = false);

protected:
	static void inPostFixOrder(const std::set<std::string>& elements,
	                           const xercesc::DOMElement* root,
	                           const bool includeEmbeddedDoc,
	                           std::list<xercesc::DOMElement*>& nodes);

	static void inDocumentOrder(const std::set<std::string>& elements,
	                            const xercesc::DOMElement* root,
	                            const bool includeEmbeddedDoc,
	                            std::list<xercesc::DOMElement*>& nodes);


};

// create a prefix from a given element - useful for copying namespace information
#define XML_PREFIX(element) X(element->getPrefix() ? X(element->getPrefix()).str() + ":" : "")

class USCXML_API X {
public :

	X(X const &other) {
		_localForm = other._localForm;
		_otherForm = xercesc::XMLString::replicate(other._otherForm);
		_deallocOther = true;
	}
	void operator=(X const &other) { // did we maybe leak before?
		_localForm = other._localForm;
		_otherForm = xercesc::XMLString::replicate(other._otherForm);
		_deallocOther = true;
	}

	X(const XMLCh* const toTranscode) {
		if (toTranscode != NULL) {
			// Call the private transcoding method
			char* tmp = xercesc::XMLString::transcode(toTranscode);
			_localForm = std::string(tmp);
			xercesc::XMLString::release(&tmp);
		}
		_otherForm = NULL;
		_deallocOther = false;
	}

	X(const std::string& fromTranscode) {
		// Call the private transcoding method
		_localForm = fromTranscode;
		_otherForm = xercesc::XMLString::transcode(fromTranscode.c_str());
		_deallocOther = true;
	}

	X(const char* const fromTranscode) {
		// Call the private transcoding method
		_localForm = fromTranscode;
		_otherForm = xercesc::XMLString::transcode(fromTranscode);
		_deallocOther = true;
	}

	X(char* fromTranscode) {
		// Call the private transcoding method
		_localForm = fromTranscode;
		_otherForm = xercesc::XMLString::transcode(fromTranscode);
		_deallocOther = true;
	}

	X() {
		_otherForm = NULL;
		_deallocOther = false;
	}

	~X() {
		if (_deallocOther)
			xercesc::XMLString::release(&_otherForm);
	}

	const std::string& str() const {
		return _localForm;
	}

	operator const XMLCh* () {
		assert(_otherForm != NULL); // constructor with XMLCh
		return _otherForm;
	}

	operator bool () {
		return _localForm.size() > 0;
	}

	operator std::string () {
		return _localForm;
	}

protected:
	friend USCXML_API std::ostream& operator<< (std::ostream& os, const X& data);

private:
	bool _deallocOther;
	std::string _localForm;
	XMLCh* _otherForm;
};

USCXML_API std::ostream& operator<< (std::ostream& os, const X& xmlString);
USCXML_API std::ostream& operator<< (std::ostream& os, const xercesc::DOMNode& node);

}


#endif /* end of include guard: DOMUTILS_H_WK0WAEA7 */
