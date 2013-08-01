#include "JSCDocument.h"
#include "JSCNode.h"
#include "JSCNodeList.h"

namespace Arabica {
namespace DOM {

JSClassRef JSCNode::Tmpl;

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
	{ "attributes", attributesCustomAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
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

JSValueRef JSCNode::nodeNameAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCNodePrivate* privData = (struct JSCNodePrivate*)JSObjectGetPrivate(object);

	JSStringRef stringRef = JSStringCreateWithUTF8CString(privData->nativeObj->getNodeName().c_str());
	JSValueRef retVal = JSValueMakeString(ctx, stringRef);
	JSStringRelease(stringRef);
	return retVal;
}


JSValueRef JSCNode::nodeValueAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCNodePrivate* privData = (struct JSCNodePrivate*)JSObjectGetPrivate(object);

	JSStringRef stringRef = JSStringCreateWithUTF8CString(privData->nativeObj->getNodeValue().c_str());
	JSValueRef retVal = JSValueMakeString(ctx, stringRef);
	JSStringRelease(stringRef);
	return retVal;
}


bool JSCNode::nodeValueAttrSetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef value, JSValueRef* exception) {
	struct JSCNodePrivate* privData = (struct JSCNodePrivate*)JSObjectGetPrivate(thisObj);

	JSStringRef stringReflocalNodeValue = JSValueToStringCopy(ctx, value, exception);
	size_t localNodeValueMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalNodeValue);
	char* localNodeValueBuffer = new char[localNodeValueMaxSize];
	JSStringGetUTF8CString(stringReflocalNodeValue, localNodeValueBuffer, sizeof(localNodeValueBuffer));
	std::string localNodeValue(localNodeValueBuffer, localNodeValueMaxSize);
	free(localNodeValueBuffer);

	privData->nativeObj->setNodeValue(localNodeValue);
	return true;
}

JSValueRef JSCNode::nodeTypeAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCNodePrivate* privData = (struct JSCNodePrivate*)JSObjectGetPrivate(object);

	return JSValueMakeNumber(ctx, privData->nativeObj->getNodeType());
}


JSValueRef JSCNode::parentNodeAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCNodePrivate* privData = (struct JSCNodePrivate*)JSObjectGetPrivate(object);

	if (!privData->nativeObj->getParentNode()) return JSValueMakeUndefined(ctx);
	Arabica::DOM::Node<std::string>* arabicaRet = new Arabica::DOM::Node<std::string>(privData->nativeObj->getParentNode());

	JSClassRef arbaicaRetClass = JSCNode::getTmpl();

	struct JSCNode::JSCNodePrivate* retPrivData = new JSCNode::JSCNodePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = arabicaRet;

	JSObjectRef arbaicaRetObj = JSObjectMake(ctx, arbaicaRetClass, arabicaRet);
	return arbaicaRetObj;
}


JSValueRef JSCNode::childNodesAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCNodePrivate* privData = (struct JSCNodePrivate*)JSObjectGetPrivate(object);


	Arabica::DOM::NodeList<std::string>* arabicaRet = new Arabica::DOM::NodeList<std::string>(privData->nativeObj->getChildNodes());

	JSClassRef arbaicaRetClass = JSCNodeList::getTmpl();

	struct JSCNodeList::JSCNodeListPrivate* retPrivData = new JSCNodeList::JSCNodeListPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = arabicaRet;

	JSObjectRef arbaicaRetObj = JSObjectMake(ctx, arbaicaRetClass, arabicaRet);
	return arbaicaRetObj;
}


JSValueRef JSCNode::firstChildAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCNodePrivate* privData = (struct JSCNodePrivate*)JSObjectGetPrivate(object);

	if (!privData->nativeObj->getFirstChild()) return JSValueMakeUndefined(ctx);
	Arabica::DOM::Node<std::string>* arabicaRet = new Arabica::DOM::Node<std::string>(privData->nativeObj->getFirstChild());

	JSClassRef arbaicaRetClass = JSCNode::getTmpl();

	struct JSCNode::JSCNodePrivate* retPrivData = new JSCNode::JSCNodePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = arabicaRet;

	JSObjectRef arbaicaRetObj = JSObjectMake(ctx, arbaicaRetClass, arabicaRet);
	return arbaicaRetObj;
}


JSValueRef JSCNode::lastChildAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCNodePrivate* privData = (struct JSCNodePrivate*)JSObjectGetPrivate(object);

	if (!privData->nativeObj->getLastChild()) return JSValueMakeUndefined(ctx);
	Arabica::DOM::Node<std::string>* arabicaRet = new Arabica::DOM::Node<std::string>(privData->nativeObj->getLastChild());

	JSClassRef arbaicaRetClass = JSCNode::getTmpl();

	struct JSCNode::JSCNodePrivate* retPrivData = new JSCNode::JSCNodePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = arabicaRet;

	JSObjectRef arbaicaRetObj = JSObjectMake(ctx, arbaicaRetClass, arabicaRet);
	return arbaicaRetObj;
}


JSValueRef JSCNode::previousSiblingAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCNodePrivate* privData = (struct JSCNodePrivate*)JSObjectGetPrivate(object);

	if (!privData->nativeObj->getPreviousSibling()) return JSValueMakeUndefined(ctx);
	Arabica::DOM::Node<std::string>* arabicaRet = new Arabica::DOM::Node<std::string>(privData->nativeObj->getPreviousSibling());

	JSClassRef arbaicaRetClass = JSCNode::getTmpl();

	struct JSCNode::JSCNodePrivate* retPrivData = new JSCNode::JSCNodePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = arabicaRet;

	JSObjectRef arbaicaRetObj = JSObjectMake(ctx, arbaicaRetClass, arabicaRet);
	return arbaicaRetObj;
}


JSValueRef JSCNode::nextSiblingAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCNodePrivate* privData = (struct JSCNodePrivate*)JSObjectGetPrivate(object);

	if (!privData->nativeObj->getNextSibling()) return JSValueMakeUndefined(ctx);
	Arabica::DOM::Node<std::string>* arabicaRet = new Arabica::DOM::Node<std::string>(privData->nativeObj->getNextSibling());

	JSClassRef arbaicaRetClass = JSCNode::getTmpl();

	struct JSCNode::JSCNodePrivate* retPrivData = new JSCNode::JSCNodePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = arabicaRet;

	JSObjectRef arbaicaRetObj = JSObjectMake(ctx, arbaicaRetClass, arabicaRet);
	return arbaicaRetObj;
}


JSValueRef JSCNode::ownerDocumentAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCNodePrivate* privData = (struct JSCNodePrivate*)JSObjectGetPrivate(object);

	if (!privData->nativeObj->getOwnerDocument()) return JSValueMakeUndefined(ctx);
	Arabica::DOM::Document<std::string>* arabicaRet = new Arabica::DOM::Document<std::string>(privData->nativeObj->getOwnerDocument());

	JSClassRef arbaicaRetClass = JSCDocument::getTmpl();

	struct JSCDocument::JSCDocumentPrivate* retPrivData = new JSCDocument::JSCDocumentPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = arabicaRet;

	JSObjectRef arbaicaRetObj = JSObjectMake(ctx, arbaicaRetClass, arabicaRet);
	return arbaicaRetObj;
}


JSValueRef JSCNode::namespaceURIAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCNodePrivate* privData = (struct JSCNodePrivate*)JSObjectGetPrivate(object);

	JSStringRef stringRef = JSStringCreateWithUTF8CString(privData->nativeObj->getNamespaceURI().c_str());
	JSValueRef retVal = JSValueMakeString(ctx, stringRef);
	JSStringRelease(stringRef);
	return retVal;
}


JSValueRef JSCNode::prefixAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCNodePrivate* privData = (struct JSCNodePrivate*)JSObjectGetPrivate(object);

	JSStringRef stringRef = JSStringCreateWithUTF8CString(privData->nativeObj->getPrefix().c_str());
	JSValueRef retVal = JSValueMakeString(ctx, stringRef);
	JSStringRelease(stringRef);
	return retVal;
}


bool JSCNode::prefixAttrSetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef value, JSValueRef* exception) {
	struct JSCNodePrivate* privData = (struct JSCNodePrivate*)JSObjectGetPrivate(thisObj);

	JSStringRef stringReflocalPrefix = JSValueToStringCopy(ctx, value, exception);
	size_t localPrefixMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalPrefix);
	char* localPrefixBuffer = new char[localPrefixMaxSize];
	JSStringGetUTF8CString(stringReflocalPrefix, localPrefixBuffer, sizeof(localPrefixBuffer));
	std::string localPrefix(localPrefixBuffer, localPrefixMaxSize);
	free(localPrefixBuffer);

	privData->nativeObj->setPrefix(localPrefix);
	return true;
}

JSValueRef JSCNode::localNameAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCNodePrivate* privData = (struct JSCNodePrivate*)JSObjectGetPrivate(object);

	JSStringRef stringRef = JSStringCreateWithUTF8CString(privData->nativeObj->getLocalName().c_str());
	JSValueRef retVal = JSValueMakeString(ctx, stringRef);
	JSStringRelease(stringRef);
	return retVal;
}

JSValueRef JSCNode::ELEMENT_NODEConstGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef *exception) {
	return JSValueMakeNumber(ctx, 1);
}

JSValueRef JSCNode::ATTRIBUTE_NODEConstGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef *exception) {
	return JSValueMakeNumber(ctx, 2);
}

JSValueRef JSCNode::TEXT_NODEConstGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef *exception) {
	return JSValueMakeNumber(ctx, 3);
}

JSValueRef JSCNode::CDATA_SECTION_NODEConstGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef *exception) {
	return JSValueMakeNumber(ctx, 4);
}

JSValueRef JSCNode::ENTITY_REFERENCE_NODEConstGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef *exception) {
	return JSValueMakeNumber(ctx, 5);
}

JSValueRef JSCNode::ENTITY_NODEConstGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef *exception) {
	return JSValueMakeNumber(ctx, 6);
}

JSValueRef JSCNode::PROCESSING_INSTRUCTION_NODEConstGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef *exception) {
	return JSValueMakeNumber(ctx, 7);
}

JSValueRef JSCNode::COMMENT_NODEConstGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef *exception) {
	return JSValueMakeNumber(ctx, 8);
}

JSValueRef JSCNode::DOCUMENT_NODEConstGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef *exception) {
	return JSValueMakeNumber(ctx, 9);
}

JSValueRef JSCNode::DOCUMENT_TYPE_NODEConstGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef *exception) {
	return JSValueMakeNumber(ctx, 10);
}

JSValueRef JSCNode::DOCUMENT_FRAGMENT_NODEConstGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef *exception) {
	return JSValueMakeNumber(ctx, 11);
}

JSValueRef JSCNode::NOTATION_NODEConstGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef *exception) {
	return JSValueMakeNumber(ctx, 12);
}

JSValueRef JSCNode::insertBeforeCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 2) {
		std::string errorMsg = "Wrong number of arguments in insertBefore";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCNodePrivate* privData = (struct JSCNodePrivate*)JSObjectGetPrivate(thisObj);

	Arabica::DOM::Node<std::string>* localNewChild = ((struct JSCNode::JSCNodePrivate*)JSObjectGetPrivate(thisObj))->nativeObj;
	Arabica::DOM::Node<std::string>* localRefChild = ((struct JSCNode::JSCNodePrivate*)JSObjectGetPrivate(thisObj))->nativeObj;

	Arabica::DOM::Node<std::string>* retVal = new Arabica::DOM::Node<std::string>(privData->nativeObj->insertBefore(*localNewChild, *localRefChild));
	JSClassRef retClass = JSCNode::getTmpl();

	struct JSCNode::JSCNodePrivate* retPrivData = new JSCNode::JSCNodePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

	return retObj;

}

JSValueRef JSCNode::replaceChildCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 2) {
		std::string errorMsg = "Wrong number of arguments in replaceChild";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCNodePrivate* privData = (struct JSCNodePrivate*)JSObjectGetPrivate(thisObj);

	Arabica::DOM::Node<std::string>* localNewChild = ((struct JSCNode::JSCNodePrivate*)JSObjectGetPrivate(thisObj))->nativeObj;
	Arabica::DOM::Node<std::string>* localOldChild = ((struct JSCNode::JSCNodePrivate*)JSObjectGetPrivate(thisObj))->nativeObj;

	Arabica::DOM::Node<std::string>* retVal = new Arabica::DOM::Node<std::string>(privData->nativeObj->replaceChild(*localNewChild, *localOldChild));
	JSClassRef retClass = JSCNode::getTmpl();

	struct JSCNode::JSCNodePrivate* retPrivData = new JSCNode::JSCNodePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

	return retObj;

}

JSValueRef JSCNode::removeChildCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 1) {
		std::string errorMsg = "Wrong number of arguments in removeChild";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCNodePrivate* privData = (struct JSCNodePrivate*)JSObjectGetPrivate(thisObj);

	Arabica::DOM::Node<std::string>* localOldChild = ((struct JSCNode::JSCNodePrivate*)JSObjectGetPrivate(thisObj))->nativeObj;

	Arabica::DOM::Node<std::string>* retVal = new Arabica::DOM::Node<std::string>(privData->nativeObj->removeChild(*localOldChild));
	JSClassRef retClass = JSCNode::getTmpl();

	struct JSCNode::JSCNodePrivate* retPrivData = new JSCNode::JSCNodePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

	return retObj;

}

JSValueRef JSCNode::appendChildCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 1) {
		std::string errorMsg = "Wrong number of arguments in appendChild";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCNodePrivate* privData = (struct JSCNodePrivate*)JSObjectGetPrivate(thisObj);

	Arabica::DOM::Node<std::string>* localNewChild = ((struct JSCNode::JSCNodePrivate*)JSObjectGetPrivate(thisObj))->nativeObj;

	Arabica::DOM::Node<std::string>* retVal = new Arabica::DOM::Node<std::string>(privData->nativeObj->appendChild(*localNewChild));
	JSClassRef retClass = JSCNode::getTmpl();

	struct JSCNode::JSCNodePrivate* retPrivData = new JSCNode::JSCNodePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

	return retObj;

}

JSValueRef JSCNode::hasChildNodesCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {

	struct JSCNodePrivate* privData = (struct JSCNodePrivate*)JSObjectGetPrivate(thisObj);


	bool retVal = privData->nativeObj->hasChildNodes();

	JSValueRef jscRetVal = JSValueMakeBoolean(ctx, retVal);
	return jscRetVal;
}

JSValueRef JSCNode::cloneNodeCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 1) {
		std::string errorMsg = "Wrong number of arguments in cloneNode";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCNodePrivate* privData = (struct JSCNodePrivate*)JSObjectGetPrivate(thisObj);

	bool localDeep = JSValueToBoolean(ctx, arguments[0]);

	Arabica::DOM::Node<std::string>* retVal = new Arabica::DOM::Node<std::string>(privData->nativeObj->cloneNode(localDeep));
	JSClassRef retClass = JSCNode::getTmpl();

	struct JSCNode::JSCNodePrivate* retPrivData = new JSCNode::JSCNodePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

	return retObj;

}

JSValueRef JSCNode::normalizeCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {

	struct JSCNodePrivate* privData = (struct JSCNodePrivate*)JSObjectGetPrivate(thisObj);


	privData->nativeObj->normalize();

	JSValueRef jscRetVal = JSValueMakeUndefined(ctx);
	return jscRetVal;
}

JSValueRef JSCNode::isSupportedCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 2) {
		std::string errorMsg = "Wrong number of arguments in isSupported";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCNodePrivate* privData = (struct JSCNodePrivate*)JSObjectGetPrivate(thisObj);

	JSStringRef stringReflocalFeature = JSValueToStringCopy(ctx, arguments[0], exception);
	size_t localFeatureMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalFeature);
	char* localFeatureBuffer = new char[localFeatureMaxSize];
	JSStringGetUTF8CString(stringReflocalFeature, localFeatureBuffer, sizeof(localFeatureBuffer));
	std::string localFeature(localFeatureBuffer, localFeatureMaxSize);
	free(localFeatureBuffer);

	JSStringRef stringReflocalVersion = JSValueToStringCopy(ctx, arguments[1], exception);
	size_t localVersionMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalVersion);
	char* localVersionBuffer = new char[localVersionMaxSize];
	JSStringGetUTF8CString(stringReflocalVersion, localVersionBuffer, sizeof(localVersionBuffer));
	std::string localVersion(localVersionBuffer, localVersionMaxSize);
	free(localVersionBuffer);


	bool retVal = privData->nativeObj->isSupported(localFeature, localVersion);

	JSValueRef jscRetVal = JSValueMakeBoolean(ctx, retVal);
	return jscRetVal;
}

JSValueRef JSCNode::hasAttributesCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {

	struct JSCNodePrivate* privData = (struct JSCNodePrivate*)JSObjectGetPrivate(thisObj);


	bool retVal = privData->nativeObj->hasAttributes();

	JSValueRef jscRetVal = JSValueMakeBoolean(ctx, retVal);
	return jscRetVal;
}


}
}
