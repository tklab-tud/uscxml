#include "JSCNamedNodeMap.h"
#include "JSCNode.h"

namespace Arabica {
namespace DOM {

JSClassRef JSCNamedNodeMap::Tmpl;

JSStaticValue JSCNamedNodeMap::staticValues[] = {
	{ "length", lengthAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },

	{ 0, 0, 0, 0 }
};

JSStaticFunction JSCNamedNodeMap::staticFunctions[] = {
	{ "getNamedItem", getNamedItemCallback, kJSPropertyAttributeDontDelete },
	{ "setNamedItem", setNamedItemCallback, kJSPropertyAttributeDontDelete },
	{ "removeNamedItem", removeNamedItemCallback, kJSPropertyAttributeDontDelete },
	{ "item", itemCallback, kJSPropertyAttributeDontDelete },
	{ "getNamedItemNS", getNamedItemNSCallback, kJSPropertyAttributeDontDelete },
	{ "setNamedItemNS", setNamedItemNSCallback, kJSPropertyAttributeDontDelete },
	{ "removeNamedItemNS", removeNamedItemNSCallback, kJSPropertyAttributeDontDelete },
	{ 0, 0, 0 }
};

JSValueRef JSCNamedNodeMap::lengthAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCNamedNodeMapPrivate* privData = (struct JSCNamedNodeMapPrivate*)JSObjectGetPrivate(object);

	return JSValueMakeNumber(ctx, privData->nativeObj->getLength());
}

JSValueRef JSCNamedNodeMap::getNamedItemCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 1) {
		std::string errorMsg = "Wrong number of arguments in getNamedItem";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCNamedNodeMapPrivate* privData = (struct JSCNamedNodeMapPrivate*)JSObjectGetPrivate(thisObj);

	JSStringRef stringReflocalName = JSValueToStringCopy(ctx, arguments[0], exception);
	size_t localNameMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalName);
	char* localNameBuffer = new char[localNameMaxSize];
	JSStringGetUTF8CString(stringReflocalName, localNameBuffer, sizeof(localNameBuffer));
	std::string localName(localNameBuffer, localNameMaxSize);
	free(localNameBuffer);


	Arabica::DOM::Node<std::string>* retVal = new Arabica::DOM::Node<std::string>(privData->nativeObj->getNamedItem(localName));
	JSClassRef retClass = JSCNode::getTmpl();

	struct JSCNode::JSCNodePrivate* retPrivData = new JSCNode::JSCNodePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

	return retObj;

}

JSValueRef JSCNamedNodeMap::setNamedItemCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 1) {
		std::string errorMsg = "Wrong number of arguments in setNamedItem";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCNamedNodeMapPrivate* privData = (struct JSCNamedNodeMapPrivate*)JSObjectGetPrivate(thisObj);

	Arabica::DOM::Node<std::string>* localArg = ((struct JSCNode::JSCNodePrivate*)JSObjectGetPrivate(thisObj))->nativeObj;

	Arabica::DOM::Node<std::string>* retVal = new Arabica::DOM::Node<std::string>(privData->nativeObj->setNamedItem(*localArg));
	JSClassRef retClass = JSCNode::getTmpl();

	struct JSCNode::JSCNodePrivate* retPrivData = new JSCNode::JSCNodePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

	return retObj;

}

JSValueRef JSCNamedNodeMap::removeNamedItemCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 1) {
		std::string errorMsg = "Wrong number of arguments in removeNamedItem";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCNamedNodeMapPrivate* privData = (struct JSCNamedNodeMapPrivate*)JSObjectGetPrivate(thisObj);

	JSStringRef stringReflocalName = JSValueToStringCopy(ctx, arguments[0], exception);
	size_t localNameMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalName);
	char* localNameBuffer = new char[localNameMaxSize];
	JSStringGetUTF8CString(stringReflocalName, localNameBuffer, sizeof(localNameBuffer));
	std::string localName(localNameBuffer, localNameMaxSize);
	free(localNameBuffer);


	Arabica::DOM::Node<std::string>* retVal = new Arabica::DOM::Node<std::string>(privData->nativeObj->removeNamedItem(localName));
	JSClassRef retClass = JSCNode::getTmpl();

	struct JSCNode::JSCNodePrivate* retPrivData = new JSCNode::JSCNodePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

	return retObj;

}

JSValueRef JSCNamedNodeMap::itemCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 1) {
		std::string errorMsg = "Wrong number of arguments in item";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCNamedNodeMapPrivate* privData = (struct JSCNamedNodeMapPrivate*)JSObjectGetPrivate(thisObj);

	unsigned long localIndex = (unsigned long)JSValueToNumber(ctx, arguments[0], exception);

	Arabica::DOM::Node<std::string>* retVal = new Arabica::DOM::Node<std::string>(privData->nativeObj->item(localIndex));
	JSClassRef retClass = JSCNode::getTmpl();

	struct JSCNode::JSCNodePrivate* retPrivData = new JSCNode::JSCNodePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

	return retObj;

}

JSValueRef JSCNamedNodeMap::getNamedItemNSCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 2) {
		std::string errorMsg = "Wrong number of arguments in getNamedItemNS";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCNamedNodeMapPrivate* privData = (struct JSCNamedNodeMapPrivate*)JSObjectGetPrivate(thisObj);

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


	Arabica::DOM::Node<std::string>* retVal = new Arabica::DOM::Node<std::string>(privData->nativeObj->getNamedItemNS(localNamespaceURI, localLocalName));
	JSClassRef retClass = JSCNode::getTmpl();

	struct JSCNode::JSCNodePrivate* retPrivData = new JSCNode::JSCNodePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

	return retObj;

}

JSValueRef JSCNamedNodeMap::setNamedItemNSCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 1) {
		std::string errorMsg = "Wrong number of arguments in setNamedItemNS";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCNamedNodeMapPrivate* privData = (struct JSCNamedNodeMapPrivate*)JSObjectGetPrivate(thisObj);

	Arabica::DOM::Node<std::string>* localArg = ((struct JSCNode::JSCNodePrivate*)JSObjectGetPrivate(thisObj))->nativeObj;

	Arabica::DOM::Node<std::string>* retVal = new Arabica::DOM::Node<std::string>(privData->nativeObj->setNamedItemNS(*localArg));
	JSClassRef retClass = JSCNode::getTmpl();

	struct JSCNode::JSCNodePrivate* retPrivData = new JSCNode::JSCNodePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

	return retObj;

}

JSValueRef JSCNamedNodeMap::removeNamedItemNSCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 2) {
		std::string errorMsg = "Wrong number of arguments in removeNamedItemNS";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCNamedNodeMapPrivate* privData = (struct JSCNamedNodeMapPrivate*)JSObjectGetPrivate(thisObj);

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


	Arabica::DOM::Node<std::string>* retVal = new Arabica::DOM::Node<std::string>(privData->nativeObj->removeNamedItemNS(localNamespaceURI, localLocalName));
	JSClassRef retClass = JSCNode::getTmpl();

	struct JSCNode::JSCNodePrivate* retPrivData = new JSCNode::JSCNodePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

	return retObj;

}


}
}
