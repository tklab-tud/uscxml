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

	static const XERCESC_NS::DOMElement* getNearestAncestor(const XERCESC_NS::DOMNode* node, const std::string tagName);
	static bool isDescendant(const XERCESC_NS::DOMNode* s1, const XERCESC_NS::DOMNode* s2);

	static bool hasIntersection(const std::list<XERCESC_NS::DOMElement*>& l1,
	                            const std::list<XERCESC_NS::DOMElement*>& l2);
	static bool isMember(const XERCESC_NS::DOMElement* node, const std::list<XERCESC_NS::DOMElement*>& list);
	static bool isMember(const XERCESC_NS::DOMNode* node, const std::list<XERCESC_NS::DOMNode*>& list);
	static bool isMember(const XERCESC_NS::DOMNode* node, const XERCESC_NS::DOMNodeList* list);

	static std::string xPathForNode(const XERCESC_NS::DOMNode* node,
	                                const std::string& ns = "");
	static std::string idForNode(const XERCESC_NS::DOMNode* node);

	static std::list<XERCESC_NS::DOMNode*> getElementsByType(const XERCESC_NS::DOMNode* root,
	        XERCESC_NS::DOMNode::NodeType type);

	static std::list<XERCESC_NS::DOMElement*> inPostFixOrder(const std::set<std::string>& elements,
	        const XERCESC_NS::DOMElement* root,
	        const bool includeEmbeddedDoc = false);

	static std::list<XERCESC_NS::DOMElement*> inDocumentOrder(const std::set<std::string>& elements,
	        const XERCESC_NS::DOMElement* root,
	        const bool includeEmbeddedDoc = false);

	static std::list<XERCESC_NS::DOMElement*> filterChildElements(const std::string& tagName,
	        const XERCESC_NS::DOMElement* node,
	        bool recurse = false);

	static std::list<XERCESC_NS::DOMElement*> filterChildElements(const std::string& tagName,
	        const std::list<XERCESC_NS::DOMElement*>& nodeSet,
	        bool recurse = false);

	static std::list<XERCESC_NS::DOMNode*> filterChildType(const XERCESC_NS::DOMNode::NodeType type,
	        const XERCESC_NS::DOMNode* node,
	        bool recurse = false);

	static std::list<XERCESC_NS::DOMNode*> filterChildType(const XERCESC_NS::DOMNode::NodeType type,
	        const std::list<XERCESC_NS::DOMNode*>& nodeSet,
	        bool recurse = false);

protected:
	static void inPostFixOrder(const std::set<std::string>& elements,
	                           const XERCESC_NS::DOMElement* root,
	                           const bool includeEmbeddedDoc,
	                           std::list<XERCESC_NS::DOMElement*>& nodes);

	static void inDocumentOrder(const std::set<std::string>& elements,
	                            const XERCESC_NS::DOMElement* root,
	                            const bool includeEmbeddedDoc,
	                            std::list<XERCESC_NS::DOMElement*>& nodes);


};

// create a prefix from a given element - useful for copying namespace information
#define XML_PREFIX(element) X(element->getPrefix() ? X(element->getPrefix()).str() + ":" : "")

#if 1
/**
 * @todo: More performant XercesStrings
 * https://alfps.wordpress.com/2010/05/27/cppx-xerces-strings-simplified-by-ownership-part-i/
 */

class USCXML_API X {
public :

	X(X const &other) {

		_localForm = other._localForm;
		_unicodeForm = XERCESC_NS::XMLString::replicate(other._unicodeForm);
		_deallocOther = true;
	}
	void operator=(X const &other) { // did we maybe leak before?

		_localForm = other._localForm;
		_unicodeForm = XERCESC_NS::XMLString::replicate(other._unicodeForm);
		_deallocOther = true;
	}

	X(const XMLCh* const toTranscode) {

		if (toTranscode != NULL) {
			// Call the private transcoding method
			char* tmp = XERCESC_NS::XMLString::transcode(toTranscode);
			_localForm = std::string(tmp);
			XERCESC_NS::XMLString::release(&tmp);
		}
		_unicodeForm = NULL;
		_deallocOther = false;
	}

	X(const std::string& fromTranscode) {

		// Call the private transcoding method
		_localForm = fromTranscode;
		_unicodeForm = XERCESC_NS::XMLString::transcode(fromTranscode.c_str());
		_deallocOther = true;
	}

	X(const char* const fromTranscode) {

		// Call the private transcoding method
		_localForm = fromTranscode;
		_unicodeForm = XERCESC_NS::XMLString::transcode(fromTranscode);
		_deallocOther = true;
	}

	X(char* fromTranscode) {

		// Call the private transcoding method
		_localForm = fromTranscode;
		_unicodeForm = XERCESC_NS::XMLString::transcode(fromTranscode);
		_deallocOther = true;
	}

	X() {

		_unicodeForm = NULL;
		_deallocOther = false;
	}

	~X() {

		if (_deallocOther)
			XERCESC_NS::XMLString::release(&_unicodeForm);
	}

	const std::string& str() const {
		return _localForm;
	}

	operator const XMLCh* () {
		assert(_unicodeForm != NULL); // constructor with XMLCh
		return _unicodeForm;
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
	XMLCh* _unicodeForm;
};

#else

class USCXML_API X {
public :
	X() {
	}

	void operator=(X const &other) {
		localForm = other.localForm;
		if (unicodeForm != NULL) {
			XERCESC_NS::XMLString::release(&unicodeForm);
		}
		unicodeForm = XERCESC_NS::XMLString::replicate(other.unicodeForm);
	}

	X(X const &other) {
		localForm = other.localForm;
		unicodeForm = XERCESC_NS::XMLString::replicate(other.unicodeForm);
	}

	X(const char* const toTranscode) {
		if (toTranscode != NULL) {
			localForm = toTranscode;
			unicodeForm = XERCESC_NS::XMLString::transcode(toTranscode);
		}
	}

	X(const XMLCh* toTranscode) {
		if (toTranscode != NULL) {
			unicodeForm = XERCESC_NS::XMLString::replicate(toTranscode);
			localForm = XERCESC_NS::XMLString::transcode(toTranscode);
		}
	}

	X(const std::string& toTranscode) {
		localForm = toTranscode;
		unicodeForm = XERCESC_NS::XMLString::transcode(toTranscode.c_str());
	}

	~X() {
		if (unicodeForm != NULL) {
			XERCESC_NS::XMLString::release(&unicodeForm);
		}
	}

	operator XMLCh* () const {
		return unicodeForm;
	}

	operator const std::string& () {
		return localForm;
	}

	const std::string& str() const {
		return localForm;
	}

	const XMLCh* unicode() const {
		return unicodeForm;
	}


protected:
	friend USCXML_API std::ostream& operator<< (std::ostream& os, const X& data);

private:
	XMLCh* unicodeForm = NULL;
	std::string localForm;

};

#endif

#if 0
static const X kElementScxmlName = X("scxml");
static const X kElementStateName = X("state");
static const X kElementParallelName = X("parallel");
static const X kElementTransitionName = X("transition");
static const X kElementInitialName = X("initial");
static const X kElementFinalName = X("final");
static const X kElementOnEntryName = X("onentry");
static const X kElementOnExitName = X("onexit");
static const X kElementHistoryName = X("history");

static const X kElementRaiseName = X("raise");
static const X kElementIfName = X("if");
static const X kElementElseIfName = X("elseif");
static const X kElementElseName = X("else");
static const X kElementForEachName = X("foreach");
static const X kElementLogName = X("log");

static const X kElementDataModelName = X("datamodel");
static const X kElementDataName = X("data");
static const X kElementAssignName = X("assign");
static const X kElementContentName = X("content");
static const X kElementParamName = X("param");
static const X kElementScriptName = X("script");
#endif

USCXML_API std::ostream& operator<< (std::ostream& os, const X& xmlString);
USCXML_API std::ostream& operator<< (std::ostream& os, const XERCESC_NS::DOMNode& node);

}


#endif /* end of include guard: DOMUTILS_H_WK0WAEA7 */
