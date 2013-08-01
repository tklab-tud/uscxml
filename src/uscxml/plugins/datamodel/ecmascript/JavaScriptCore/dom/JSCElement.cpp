#include "JSCAttr.h"
#include "JSCElement.h"
#include "JSCNode.h"
#include "JSCNodeList.h"

namespace Arabica {
namespace DOM {

JSClassRef JSCElement::Tmpl;

JSStaticValue JSCElement::staticValues[] = {
	{ "tagName", tagNameAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },

	{ 0, 0, 0, 0 }
};

JSStaticFunction JSCElement::staticFunctions[] = {
	{ "getAttribute", getAttributeCallback, kJSPropertyAttributeDontDelete },
	{ "setAttribute", setAttributeCallback, kJSPropertyAttributeDontDelete },
	{ "removeAttribute", removeAttributeCallback, kJSPropertyAttributeDontDelete },
	{ "getAttributeNode", getAttributeNodeCallback, kJSPropertyAttributeDontDelete },
	{ "setAttributeNode", setAttributeNodeCallback, kJSPropertyAttributeDontDelete },
	{ "removeAttributeNode", removeAttributeNodeCallback, kJSPropertyAttributeDontDelete },
	{ "getElementsByTagName", getElementsByTagNameCallback, kJSPropertyAttributeDontDelete },
	{ "getAttributeNS", getAttributeNSCallback, kJSPropertyAttributeDontDelete },
	{ "setAttributeNS", setAttributeNSCallback, kJSPropertyAttributeDontDelete },
	{ "removeAttributeNS", removeAttributeNSCallback, kJSPropertyAttributeDontDelete },
	{ "getAttributeNodeNS", getAttributeNodeNSCallback, kJSPropertyAttributeDontDelete },
	{ "setAttributeNodeNS", setAttributeNodeNSCallback, kJSPropertyAttributeDontDelete },
	{ "getElementsByTagNameNS", getElementsByTagNameNSCallback, kJSPropertyAttributeDontDelete },
	{ "hasAttribute", hasAttributeCallback, kJSPropertyAttributeDontDelete },
	{ "hasAttributeNS", hasAttributeNSCallback, kJSPropertyAttributeDontDelete },
	{ 0, 0, 0 }
};

JSValueRef JSCElement::tagNameAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCElementPrivate* privData = (struct JSCElementPrivate*)JSObjectGetPrivate(object);

	JSStringRef stringRef = JSStringCreateWithUTF8CString(privData->nativeObj->getTagName().c_str());
	JSValueRef retVal = JSValueMakeString(ctx, stringRef);
	JSStringRelease(stringRef);
	return retVal;
}

JSValueRef JSCElement::getAttributeCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 1) {
		std::string errorMsg = "Wrong number of arguments in getAttribute";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCElementPrivate* privData = (struct JSCElementPrivate*)JSObjectGetPrivate(thisObj);

	JSStringRef stringReflocalName = JSValueToStringCopy(ctx, arguments[0], exception);
	size_t localNameMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalName);
	char* localNameBuffer = new char[localNameMaxSize];
	JSStringGetUTF8CString(stringReflocalName, localNameBuffer, sizeof(localNameBuffer));
	std::string localName(localNameBuffer, localNameMaxSize);
	free(localNameBuffer);


	std::string retVal = privData->nativeObj->getAttribute(localName);

	JSStringRef jscString = JSStringCreateWithUTF8CString(retVal.c_str());
	JSValueRef jscRetVal = JSValueMakeString(ctx, jscString);
	JSStringRelease(jscString);
	return jscRetVal;
}

JSValueRef JSCElement::setAttributeCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 2) {
		std::string errorMsg = "Wrong number of arguments in setAttribute";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCElementPrivate* privData = (struct JSCElementPrivate*)JSObjectGetPrivate(thisObj);

	JSStringRef stringReflocalName = JSValueToStringCopy(ctx, arguments[0], exception);
	size_t localNameMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalName);
	char* localNameBuffer = new char[localNameMaxSize];
	JSStringGetUTF8CString(stringReflocalName, localNameBuffer, sizeof(localNameBuffer));
	std::string localName(localNameBuffer, localNameMaxSize);
	free(localNameBuffer);

	JSStringRef stringReflocalValue = JSValueToStringCopy(ctx, arguments[1], exception);
	size_t localValueMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalValue);
	char* localValueBuffer = new char[localValueMaxSize];
	JSStringGetUTF8CString(stringReflocalValue, localValueBuffer, sizeof(localValueBuffer));
	std::string localValue(localValueBuffer, localValueMaxSize);
	free(localValueBuffer);


	privData->nativeObj->setAttribute(localName, localValue);

	JSValueRef jscRetVal = JSValueMakeUndefined(ctx);
	return jscRetVal;
}

JSValueRef JSCElement::removeAttributeCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 1) {
		std::string errorMsg = "Wrong number of arguments in removeAttribute";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCElementPrivate* privData = (struct JSCElementPrivate*)JSObjectGetPrivate(thisObj);

	JSStringRef stringReflocalName = JSValueToStringCopy(ctx, arguments[0], exception);
	size_t localNameMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalName);
	char* localNameBuffer = new char[localNameMaxSize];
	JSStringGetUTF8CString(stringReflocalName, localNameBuffer, sizeof(localNameBuffer));
	std::string localName(localNameBuffer, localNameMaxSize);
	free(localNameBuffer);


	privData->nativeObj->removeAttribute(localName);

	JSValueRef jscRetVal = JSValueMakeUndefined(ctx);
	return jscRetVal;
}

JSValueRef JSCElement::getAttributeNodeCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 1) {
		std::string errorMsg = "Wrong number of arguments in getAttributeNode";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCElementPrivate* privData = (struct JSCElementPrivate*)JSObjectGetPrivate(thisObj);

	JSStringRef stringReflocalName = JSValueToStringCopy(ctx, arguments[0], exception);
	size_t localNameMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalName);
	char* localNameBuffer = new char[localNameMaxSize];
	JSStringGetUTF8CString(stringReflocalName, localNameBuffer, sizeof(localNameBuffer));
	std::string localName(localNameBuffer, localNameMaxSize);
	free(localNameBuffer);


	Arabica::DOM::Attr<std::string>* retVal = new Arabica::DOM::Attr<std::string>(privData->nativeObj->getAttributeNode(localName));
	JSClassRef retClass = JSCAttr::getTmpl();

	struct JSCAttr::JSCAttrPrivate* retPrivData = new JSCAttr::JSCAttrPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

	return retObj;

}

JSValueRef JSCElement::setAttributeNodeCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 1) {
		std::string errorMsg = "Wrong number of arguments in setAttributeNode";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCElementPrivate* privData = (struct JSCElementPrivate*)JSObjectGetPrivate(thisObj);

	Arabica::DOM::Attr<std::string>* localNewAttr = ((struct JSCAttr::JSCAttrPrivate*)JSObjectGetPrivate(thisObj))->nativeObj;

	Arabica::DOM::Attr<std::string>* retVal = new Arabica::DOM::Attr<std::string>(privData->nativeObj->setAttributeNode(*localNewAttr));
	JSClassRef retClass = JSCAttr::getTmpl();

	struct JSCAttr::JSCAttrPrivate* retPrivData = new JSCAttr::JSCAttrPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

	return retObj;

}

JSValueRef JSCElement::removeAttributeNodeCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 1) {
		std::string errorMsg = "Wrong number of arguments in removeAttributeNode";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCElementPrivate* privData = (struct JSCElementPrivate*)JSObjectGetPrivate(thisObj);

	Arabica::DOM::Attr<std::string>* localOldAttr = ((struct JSCAttr::JSCAttrPrivate*)JSObjectGetPrivate(thisObj))->nativeObj;

	Arabica::DOM::Attr<std::string>* retVal = new Arabica::DOM::Attr<std::string>(privData->nativeObj->removeAttributeNode(*localOldAttr));
	JSClassRef retClass = JSCAttr::getTmpl();

	struct JSCAttr::JSCAttrPrivate* retPrivData = new JSCAttr::JSCAttrPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

	return retObj;

}

JSValueRef JSCElement::getElementsByTagNameCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 1) {
		std::string errorMsg = "Wrong number of arguments in getElementsByTagName";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCElementPrivate* privData = (struct JSCElementPrivate*)JSObjectGetPrivate(thisObj);

	JSStringRef stringReflocalName = JSValueToStringCopy(ctx, arguments[0], exception);
	size_t localNameMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalName);
	char* localNameBuffer = new char[localNameMaxSize];
	JSStringGetUTF8CString(stringReflocalName, localNameBuffer, sizeof(localNameBuffer));
	std::string localName(localNameBuffer, localNameMaxSize);
	free(localNameBuffer);


	Arabica::DOM::NodeList<std::string>* retVal = new Arabica::DOM::NodeList<std::string>(privData->nativeObj->getElementsByTagName(localName));
	JSClassRef retClass = JSCNodeList::getTmpl();

	struct JSCNodeList::JSCNodeListPrivate* retPrivData = new JSCNodeList::JSCNodeListPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

	return retObj;

}

JSValueRef JSCElement::getAttributeNSCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 2) {
		std::string errorMsg = "Wrong number of arguments in getAttributeNS";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCElementPrivate* privData = (struct JSCElementPrivate*)JSObjectGetPrivate(thisObj);

	JSStringRef stringReflocalNamespaceURI = JSValueToStringCopy(ctx, arguments[0], exception);
	size_t localNamespaceURIMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalNamespaceURI);
	char* localNamespaceURIBuffer = new char[localNamespaceURIMaxSize];
	JSStringGetUTF8CString(stringReflocalNamespaceURI, localNamespaceURIBuffer, sizeof(localNamespaceURIBuffer));
	std::string localNamespaceURI(localNamespaceURIBuffer, localNamespaceURIMaxSize);
	free(localNamespaceURIBuffer);

	JSStringRef stringReflocalLocalName = JSValueToStringCopy(ctx, arguments[1], exception);
	size_t localLocalNameMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalLocalName);
	char* localLocalNameBuffer = new char[localLocalNameMaxSize];
	JSStringGetUTF8CString(stringReflocalLocalName, localLocalNameBuffer, sizeof(localLocalNameBuffer));
	std::string localLocalName(localLocalNameBuffer, localLocalNameMaxSize);
	free(localLocalNameBuffer);


	std::string retVal = privData->nativeObj->getAttributeNS(localNamespaceURI, localLocalName);

	JSStringRef jscString = JSStringCreateWithUTF8CString(retVal.c_str());
	JSValueRef jscRetVal = JSValueMakeString(ctx, jscString);
	JSStringRelease(jscString);
	return jscRetVal;
}

JSValueRef JSCElement::setAttributeNSCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 3) {
		std::string errorMsg = "Wrong number of arguments in setAttributeNS";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCElementPrivate* privData = (struct JSCElementPrivate*)JSObjectGetPrivate(thisObj);

	JSStringRef stringReflocalNamespaceURI = JSValueToStringCopy(ctx, arguments[0], exception);
	size_t localNamespaceURIMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalNamespaceURI);
	char* localNamespaceURIBuffer = new char[localNamespaceURIMaxSize];
	JSStringGetUTF8CString(stringReflocalNamespaceURI, localNamespaceURIBuffer, sizeof(localNamespaceURIBuffer));
	std::string localNamespaceURI(localNamespaceURIBuffer, localNamespaceURIMaxSize);
	free(localNamespaceURIBuffer);

	JSStringRef stringReflocalQualifiedName = JSValueToStringCopy(ctx, arguments[1], exception);
	size_t localQualifiedNameMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalQualifiedName);
	char* localQualifiedNameBuffer = new char[localQualifiedNameMaxSize];
	JSStringGetUTF8CString(stringReflocalQualifiedName, localQualifiedNameBuffer, sizeof(localQualifiedNameBuffer));
	std::string localQualifiedName(localQualifiedNameBuffer, localQualifiedNameMaxSize);
	free(localQualifiedNameBuffer);

	JSStringRef stringReflocalValue = JSValueToStringCopy(ctx, arguments[2], exception);
	size_t localValueMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalValue);
	char* localValueBuffer = new char[localValueMaxSize];
	JSStringGetUTF8CString(stringReflocalValue, localValueBuffer, sizeof(localValueBuffer));
	std::string localValue(localValueBuffer, localValueMaxSize);
	free(localValueBuffer);


	privData->nativeObj->setAttributeNS(localNamespaceURI, localQualifiedName, localValue);

	JSValueRef jscRetVal = JSValueMakeUndefined(ctx);
	return jscRetVal;
}

JSValueRef JSCElement::removeAttributeNSCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 2) {
		std::string errorMsg = "Wrong number of arguments in removeAttributeNS";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCElementPrivate* privData = (struct JSCElementPrivate*)JSObjectGetPrivate(thisObj);

	JSStringRef stringReflocalNamespaceURI = JSValueToStringCopy(ctx, arguments[0], exception);
	size_t localNamespaceURIMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalNamespaceURI);
	char* localNamespaceURIBuffer = new char[localNamespaceURIMaxSize];
	JSStringGetUTF8CString(stringReflocalNamespaceURI, localNamespaceURIBuffer, sizeof(localNamespaceURIBuffer));
	std::string localNamespaceURI(localNamespaceURIBuffer, localNamespaceURIMaxSize);
	free(localNamespaceURIBuffer);

	JSStringRef stringReflocalLocalName = JSValueToStringCopy(ctx, arguments[1], exception);
	size_t localLocalNameMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalLocalName);
	char* localLocalNameBuffer = new char[localLocalNameMaxSize];
	JSStringGetUTF8CString(stringReflocalLocalName, localLocalNameBuffer, sizeof(localLocalNameBuffer));
	std::string localLocalName(localLocalNameBuffer, localLocalNameMaxSize);
	free(localLocalNameBuffer);


	privData->nativeObj->removeAttributeNS(localNamespaceURI, localLocalName);

	JSValueRef jscRetVal = JSValueMakeUndefined(ctx);
	return jscRetVal;
}

JSValueRef JSCElement::getAttributeNodeNSCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 2) {
		std::string errorMsg = "Wrong number of arguments in getAttributeNodeNS";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCElementPrivate* privData = (struct JSCElementPrivate*)JSObjectGetPrivate(thisObj);

	JSStringRef stringReflocalNamespaceURI = JSValueToStringCopy(ctx, arguments[0], exception);
	size_t localNamespaceURIMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalNamespaceURI);
	char* localNamespaceURIBuffer = new char[localNamespaceURIMaxSize];
	JSStringGetUTF8CString(stringReflocalNamespaceURI, localNamespaceURIBuffer, sizeof(localNamespaceURIBuffer));
	std::string localNamespaceURI(localNamespaceURIBuffer, localNamespaceURIMaxSize);
	free(localNamespaceURIBuffer);

	JSStringRef stringReflocalLocalName = JSValueToStringCopy(ctx, arguments[1], exception);
	size_t localLocalNameMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalLocalName);
	char* localLocalNameBuffer = new char[localLocalNameMaxSize];
	JSStringGetUTF8CString(stringReflocalLocalName, localLocalNameBuffer, sizeof(localLocalNameBuffer));
	std::string localLocalName(localLocalNameBuffer, localLocalNameMaxSize);
	free(localLocalNameBuffer);


	Arabica::DOM::Attr<std::string>* retVal = new Arabica::DOM::Attr<std::string>(privData->nativeObj->getAttributeNodeNS(localNamespaceURI, localLocalName));
	JSClassRef retClass = JSCAttr::getTmpl();

	struct JSCAttr::JSCAttrPrivate* retPrivData = new JSCAttr::JSCAttrPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

	return retObj;

}

JSValueRef JSCElement::setAttributeNodeNSCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 1) {
		std::string errorMsg = "Wrong number of arguments in setAttributeNodeNS";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCElementPrivate* privData = (struct JSCElementPrivate*)JSObjectGetPrivate(thisObj);

	Arabica::DOM::Attr<std::string>* localNewAttr = ((struct JSCAttr::JSCAttrPrivate*)JSObjectGetPrivate(thisObj))->nativeObj;

	Arabica::DOM::Attr<std::string>* retVal = new Arabica::DOM::Attr<std::string>(privData->nativeObj->setAttributeNodeNS(*localNewAttr));
	JSClassRef retClass = JSCAttr::getTmpl();

	struct JSCAttr::JSCAttrPrivate* retPrivData = new JSCAttr::JSCAttrPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

	return retObj;

}

JSValueRef JSCElement::getElementsByTagNameNSCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 2) {
		std::string errorMsg = "Wrong number of arguments in getElementsByTagNameNS";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCElementPrivate* privData = (struct JSCElementPrivate*)JSObjectGetPrivate(thisObj);

	JSStringRef stringReflocalNamespaceURI = JSValueToStringCopy(ctx, arguments[0], exception);
	size_t localNamespaceURIMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalNamespaceURI);
	char* localNamespaceURIBuffer = new char[localNamespaceURIMaxSize];
	JSStringGetUTF8CString(stringReflocalNamespaceURI, localNamespaceURIBuffer, sizeof(localNamespaceURIBuffer));
	std::string localNamespaceURI(localNamespaceURIBuffer, localNamespaceURIMaxSize);
	free(localNamespaceURIBuffer);

	JSStringRef stringReflocalLocalName = JSValueToStringCopy(ctx, arguments[1], exception);
	size_t localLocalNameMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalLocalName);
	char* localLocalNameBuffer = new char[localLocalNameMaxSize];
	JSStringGetUTF8CString(stringReflocalLocalName, localLocalNameBuffer, sizeof(localLocalNameBuffer));
	std::string localLocalName(localLocalNameBuffer, localLocalNameMaxSize);
	free(localLocalNameBuffer);


	Arabica::DOM::NodeList<std::string>* retVal = new Arabica::DOM::NodeList<std::string>(privData->nativeObj->getElementsByTagNameNS(localNamespaceURI, localLocalName));
	JSClassRef retClass = JSCNodeList::getTmpl();

	struct JSCNodeList::JSCNodeListPrivate* retPrivData = new JSCNodeList::JSCNodeListPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

	return retObj;

}

JSValueRef JSCElement::hasAttributeCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 1) {
		std::string errorMsg = "Wrong number of arguments in hasAttribute";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCElementPrivate* privData = (struct JSCElementPrivate*)JSObjectGetPrivate(thisObj);

	JSStringRef stringReflocalName = JSValueToStringCopy(ctx, arguments[0], exception);
	size_t localNameMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalName);
	char* localNameBuffer = new char[localNameMaxSize];
	JSStringGetUTF8CString(stringReflocalName, localNameBuffer, sizeof(localNameBuffer));
	std::string localName(localNameBuffer, localNameMaxSize);
	free(localNameBuffer);


	bool retVal = privData->nativeObj->hasAttribute(localName);

	JSValueRef jscRetVal = JSValueMakeBoolean(ctx, retVal);
	return jscRetVal;
}

JSValueRef JSCElement::hasAttributeNSCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 2) {
		std::string errorMsg = "Wrong number of arguments in hasAttributeNS";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCElementPrivate* privData = (struct JSCElementPrivate*)JSObjectGetPrivate(thisObj);

	JSStringRef stringReflocalNamespaceURI = JSValueToStringCopy(ctx, arguments[0], exception);
	size_t localNamespaceURIMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalNamespaceURI);
	char* localNamespaceURIBuffer = new char[localNamespaceURIMaxSize];
	JSStringGetUTF8CString(stringReflocalNamespaceURI, localNamespaceURIBuffer, sizeof(localNamespaceURIBuffer));
	std::string localNamespaceURI(localNamespaceURIBuffer, localNamespaceURIMaxSize);
	free(localNamespaceURIBuffer);

	JSStringRef stringReflocalLocalName = JSValueToStringCopy(ctx, arguments[1], exception);
	size_t localLocalNameMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalLocalName);
	char* localLocalNameBuffer = new char[localLocalNameMaxSize];
	JSStringGetUTF8CString(stringReflocalLocalName, localLocalNameBuffer, sizeof(localLocalNameBuffer));
	std::string localLocalName(localLocalNameBuffer, localLocalNameMaxSize);
	free(localLocalNameBuffer);


	bool retVal = privData->nativeObj->hasAttributeNS(localNamespaceURI, localLocalName);

	JSValueRef jscRetVal = JSValueMakeBoolean(ctx, retVal);
	return jscRetVal;
}


}
}
