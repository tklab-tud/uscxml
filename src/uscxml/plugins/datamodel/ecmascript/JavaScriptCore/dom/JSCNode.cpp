#include "JSCDocument.h"
#include "JSCNamedNodeMap.h"
#include "JSCNode.h"
#include "JSCNodeList.h"

namespace Arabica {
namespace DOM {


JSStaticValue JSCNode::staticValues[] = {
	{ "nodeName", nodeNameAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "nodeValue", nodeValueAttrGetter, nodeValueAttrSetter, kJSPropertyAttributeDontDelete },
	{ "nodeType", nodeTypeAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "parentNode", parentNodeAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "childNodes", childNodesAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "firstChild", firstChildAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "lastChild", lastChildAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "previousSibling", previousSiblingAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "nextSibling", nextSiblingAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "attributes", attributesAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "ownerDocument", ownerDocumentAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "namespaceURI", namespaceURIAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "prefix", prefixAttrGetter, prefixAttrSetter, kJSPropertyAttributeDontDelete },
	{ "localName", localNameAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },

	{ "ELEMENT_NODE", ELEMENT_NODEConstGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "ATTRIBUTE_NODE", ATTRIBUTE_NODEConstGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "TEXT_NODE", TEXT_NODEConstGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "CDATA_SECTION_NODE", CDATA_SECTION_NODEConstGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "ENTITY_REFERENCE_NODE", ENTITY_REFERENCE_NODEConstGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "ENTITY_NODE", ENTITY_NODEConstGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "PROCESSING_INSTRUCTION_NODE", PROCESSING_INSTRUCTION_NODEConstGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "COMMENT_NODE", COMMENT_NODEConstGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "DOCUMENT_NODE", DOCUMENT_NODEConstGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "DOCUMENT_TYPE_NODE", DOCUMENT_TYPE_NODEConstGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "DOCUMENT_FRAGMENT_NODE", DOCUMENT_FRAGMENT_NODEConstGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "NOTATION_NODE", NOTATION_NODEConstGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ 0, 0, 0, 0 }
};

JSStaticFunction JSCNode::staticFunctions[] = {
	{ "insertBefore", insertBeforeCallback, kJSPropertyAttributeDontDelete },
	{ "replaceChild", replaceChildCallback, kJSPropertyAttributeDontDelete },
	{ "removeChild", removeChildCallback, kJSPropertyAttributeDontDelete },
	{ "appendChild", appendChildCallback, kJSPropertyAttributeDontDelete },
	{ "hasChildNodes", hasChildNodesCallback, kJSPropertyAttributeDontDelete },
	{ "cloneNode", cloneNodeCallback, kJSPropertyAttributeDontDelete },
	{ "normalize", normalizeCallback, kJSPropertyAttributeDontDelete },
	{ "isSupported", isSupportedCallback, kJSPropertyAttributeDontDelete },
	{ "hasAttributes", hasAttributesCallback, kJSPropertyAttributeDontDelete },
	{ 0, 0, 0 }
};

JSValueRef JSCNode::nodeNameAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCNodePrivate* privData = static_cast<JSCNode::JSCNodePrivate* >(JSObjectGetPrivate(thisObj));
	JSStringRef retString = JSStringCreateWithUTF8CString(privData->arabicaThis->getNodeName().c_str());
	JSValueRef retObj = JSValueMakeString(ctx, retString);
	JSStringRelease(retString);
	return retObj;

}

JSValueRef JSCNode::nodeValueAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCNodePrivate* privData = static_cast<JSCNode::JSCNodePrivate* >(JSObjectGetPrivate(thisObj));
	JSStringRef retString = JSStringCreateWithUTF8CString(privData->arabicaThis->getNodeValue().c_str());
	JSValueRef retObj = JSValueMakeString(ctx, retString);
	JSStringRelease(retString);
	return retObj;

}

JSValueRef JSCNode::nodeTypeAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCNodePrivate* privData = static_cast<JSCNode::JSCNodePrivate* >(JSObjectGetPrivate(thisObj));

	return JSValueMakeNumber(ctx, privData->arabicaThis->getNodeType());
}

JSValueRef JSCNode::parentNodeAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCNodePrivate* privData = static_cast<JSCNode::JSCNodePrivate* >(JSObjectGetPrivate(thisObj));
	Arabica::DOM::Node<std::string>* arbaicaRet = new Arabica::DOM::Node<std::string>(privData->arabicaThis->getParentNode());

	struct JSCNode::JSCNodePrivate* retPrivData = new JSCNode::JSCNodePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->arabicaThis = arbaicaRet;

	JSObjectRef arbaicaRetObj = JSObjectMake(ctx, JSCNode::getTmpl(), retPrivData);
	return arbaicaRetObj;

}

JSValueRef JSCNode::childNodesAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCNodePrivate* privData = static_cast<JSCNode::JSCNodePrivate* >(JSObjectGetPrivate(thisObj));
	Arabica::DOM::NodeList<std::string>* arbaicaRet = new Arabica::DOM::NodeList<std::string>(privData->arabicaThis->getChildNodes());

	struct JSCNodeList::JSCNodeListPrivate* retPrivData = new JSCNodeList::JSCNodeListPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->arabicaThis = arbaicaRet;

	JSObjectRef arbaicaRetObj = JSObjectMake(ctx, JSCNodeList::getTmpl(), retPrivData);
	return arbaicaRetObj;

}

JSValueRef JSCNode::firstChildAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCNodePrivate* privData = static_cast<JSCNode::JSCNodePrivate* >(JSObjectGetPrivate(thisObj));
	Arabica::DOM::Node<std::string>* arbaicaRet = new Arabica::DOM::Node<std::string>(privData->arabicaThis->getFirstChild());

	struct JSCNode::JSCNodePrivate* retPrivData = new JSCNode::JSCNodePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->arabicaThis = arbaicaRet;

	JSObjectRef arbaicaRetObj = JSObjectMake(ctx, JSCNode::getTmpl(), retPrivData);
	return arbaicaRetObj;

}

JSValueRef JSCNode::lastChildAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCNodePrivate* privData = static_cast<JSCNode::JSCNodePrivate* >(JSObjectGetPrivate(thisObj));
	Arabica::DOM::Node<std::string>* arbaicaRet = new Arabica::DOM::Node<std::string>(privData->arabicaThis->getLastChild());

	struct JSCNode::JSCNodePrivate* retPrivData = new JSCNode::JSCNodePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->arabicaThis = arbaicaRet;

	JSObjectRef arbaicaRetObj = JSObjectMake(ctx, JSCNode::getTmpl(), retPrivData);
	return arbaicaRetObj;

}

JSValueRef JSCNode::previousSiblingAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCNodePrivate* privData = static_cast<JSCNode::JSCNodePrivate* >(JSObjectGetPrivate(thisObj));
	Arabica::DOM::Node<std::string>* arbaicaRet = new Arabica::DOM::Node<std::string>(privData->arabicaThis->getPreviousSibling());

	struct JSCNode::JSCNodePrivate* retPrivData = new JSCNode::JSCNodePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->arabicaThis = arbaicaRet;

	JSObjectRef arbaicaRetObj = JSObjectMake(ctx, JSCNode::getTmpl(), retPrivData);
	return arbaicaRetObj;

}

JSValueRef JSCNode::nextSiblingAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCNodePrivate* privData = static_cast<JSCNode::JSCNodePrivate* >(JSObjectGetPrivate(thisObj));
	Arabica::DOM::Node<std::string>* arbaicaRet = new Arabica::DOM::Node<std::string>(privData->arabicaThis->getNextSibling());

	struct JSCNode::JSCNodePrivate* retPrivData = new JSCNode::JSCNodePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->arabicaThis = arbaicaRet;

	JSObjectRef arbaicaRetObj = JSObjectMake(ctx, JSCNode::getTmpl(), retPrivData);
	return arbaicaRetObj;

}

JSValueRef JSCNode::attributesAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCNodePrivate* privData = static_cast<JSCNode::JSCNodePrivate* >(JSObjectGetPrivate(thisObj));
	Arabica::DOM::NamedNodeMap<std::string>* arbaicaRet = new Arabica::DOM::NamedNodeMap<std::string>(privData->arabicaThis->getAttributes());

	struct JSCNamedNodeMap::JSCNamedNodeMapPrivate* retPrivData = new JSCNamedNodeMap::JSCNamedNodeMapPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->arabicaThis = arbaicaRet;

	JSObjectRef arbaicaRetObj = JSObjectMake(ctx, JSCNamedNodeMap::getTmpl(), retPrivData);
	return arbaicaRetObj;

}

JSValueRef JSCNode::ownerDocumentAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCNodePrivate* privData = static_cast<JSCNode::JSCNodePrivate* >(JSObjectGetPrivate(thisObj));
	Arabica::DOM::Document<std::string>* arbaicaRet = new Arabica::DOM::Document<std::string>(privData->arabicaThis->getOwnerDocument());

	struct JSCDocument::JSCDocumentPrivate* retPrivData = new JSCDocument::JSCDocumentPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->arabicaThis = arbaicaRet;

	JSObjectRef arbaicaRetObj = JSObjectMake(ctx, JSCDocument::getTmpl(), retPrivData);
	return arbaicaRetObj;

}

JSValueRef JSCNode::namespaceURIAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCNodePrivate* privData = static_cast<JSCNode::JSCNodePrivate* >(JSObjectGetPrivate(thisObj));
	JSStringRef retString = JSStringCreateWithUTF8CString(privData->arabicaThis->getNamespaceURI().c_str());
	JSValueRef retObj = JSValueMakeString(ctx, retString);
	JSStringRelease(retString);
	return retObj;

}

JSValueRef JSCNode::prefixAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCNodePrivate* privData = static_cast<JSCNode::JSCNodePrivate* >(JSObjectGetPrivate(thisObj));
	JSStringRef retString = JSStringCreateWithUTF8CString(privData->arabicaThis->getPrefix().c_str());
	JSValueRef retObj = JSValueMakeString(ctx, retString);
	JSStringRelease(retString);
	return retObj;

}

JSValueRef JSCNode::localNameAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCNodePrivate* privData = static_cast<JSCNode::JSCNodePrivate* >(JSObjectGetPrivate(thisObj));
	JSStringRef retString = JSStringCreateWithUTF8CString(privData->arabicaThis->getLocalName().c_str());
	JSValueRef retObj = JSValueMakeString(ctx, retString);
	JSStringRelease(retString);
	return retObj;

}

}
}
