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

	struct JSCNamedNodeMapPrivate* privData = (struct JSCNamedNodeMapPrivate*)JSObjectGetPrivate(thisObj);

	if (false) {
	} else if (argumentCount == 1 &&
	           JSValueIsString(ctx, arguments[0])) {
		JSStringRef stringReflocalName = JSValueToStringCopy(ctx, arguments[0], exception);
		size_t localNameMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalName);
		char* localNameBuffer = new char[localNameMaxSize];
		JSStringGetUTF8CString(stringReflocalName, localNameBuffer, localNameMaxSize);
		std::string localName(localNameBuffer);
		JSStringRelease(stringReflocalName);
		free(localNameBuffer);


		Arabica::DOM::Node<std::string>* retVal = new Arabica::DOM::Node<std::string>(privData->nativeObj->getNamedItem(localName));
		JSClassRef retClass = JSCNode::getTmpl();

		struct JSCNode::JSCNodePrivate* retPrivData = new JSCNode::JSCNodePrivate();
		retPrivData->dom = privData->dom;
		retPrivData->nativeObj = retVal;

		JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

		return retObj;

	}

	JSStringRef exceptionString = JSStringCreateWithUTF8CString("Parameter mismatch while calling getNamedItem");
	*exception = JSValueMakeString(ctx, exceptionString);
	JSStringRelease(exceptionString);
	return JSValueMakeUndefined(ctx);
}

JSValueRef JSCNamedNodeMap::setNamedItemCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {

	struct JSCNamedNodeMapPrivate* privData = (struct JSCNamedNodeMapPrivate*)JSObjectGetPrivate(thisObj);

	if (false) {
	} else if (argumentCount == 1 &&
	           JSValueIsObject(ctx, arguments[0]) && JSValueIsObjectOfClass(ctx, arguments[0], JSCNode::getTmpl())) {
		Arabica::DOM::Node<std::string>* localArg = ((struct JSCNode::JSCNodePrivate*)JSObjectGetPrivate(JSValueToObject(ctx, arguments[0], exception)))->nativeObj;

		Arabica::DOM::Node<std::string>* retVal = new Arabica::DOM::Node<std::string>(privData->nativeObj->setNamedItem(*localArg));
		JSClassRef retClass = JSCNode::getTmpl();

		struct JSCNode::JSCNodePrivate* retPrivData = new JSCNode::JSCNodePrivate();
		retPrivData->dom = privData->dom;
		retPrivData->nativeObj = retVal;

		JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

		return retObj;

	}

	JSStringRef exceptionString = JSStringCreateWithUTF8CString("Parameter mismatch while calling setNamedItem");
	*exception = JSValueMakeString(ctx, exceptionString);
	JSStringRelease(exceptionString);
	return JSValueMakeUndefined(ctx);
}

JSValueRef JSCNamedNodeMap::removeNamedItemCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {

	struct JSCNamedNodeMapPrivate* privData = (struct JSCNamedNodeMapPrivate*)JSObjectGetPrivate(thisObj);

	if (false) {
	} else if (argumentCount == 1 &&
	           JSValueIsString(ctx, arguments[0])) {
		JSStringRef stringReflocalName = JSValueToStringCopy(ctx, arguments[0], exception);
		size_t localNameMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalName);
		char* localNameBuffer = new char[localNameMaxSize];
		JSStringGetUTF8CString(stringReflocalName, localNameBuffer, localNameMaxSize);
		std::string localName(localNameBuffer);
		JSStringRelease(stringReflocalName);
		free(localNameBuffer);


		Arabica::DOM::Node<std::string>* retVal = new Arabica::DOM::Node<std::string>(privData->nativeObj->removeNamedItem(localName));
		JSClassRef retClass = JSCNode::getTmpl();

		struct JSCNode::JSCNodePrivate* retPrivData = new JSCNode::JSCNodePrivate();
		retPrivData->dom = privData->dom;
		retPrivData->nativeObj = retVal;

		JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

		return retObj;

	}

	JSStringRef exceptionString = JSStringCreateWithUTF8CString("Parameter mismatch while calling removeNamedItem");
	*exception = JSValueMakeString(ctx, exceptionString);
	JSStringRelease(exceptionString);
	return JSValueMakeUndefined(ctx);
}

JSValueRef JSCNamedNodeMap::itemCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {

	struct JSCNamedNodeMapPrivate* privData = (struct JSCNamedNodeMapPrivate*)JSObjectGetPrivate(thisObj);

	if (false) {
	} else if (argumentCount == 1 &&
	           JSValueIsNumber(ctx, arguments[0])) {
		unsigned long localIndex = (unsigned long)JSValueToNumber(ctx, arguments[0], exception);

		Arabica::DOM::Node<std::string>* retVal = new Arabica::DOM::Node<std::string>(privData->nativeObj->item(localIndex));
		JSClassRef retClass = JSCNode::getTmpl();

		struct JSCNode::JSCNodePrivate* retPrivData = new JSCNode::JSCNodePrivate();
		retPrivData->dom = privData->dom;
		retPrivData->nativeObj = retVal;

		JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

		return retObj;

	}

	JSStringRef exceptionString = JSStringCreateWithUTF8CString("Parameter mismatch while calling item");
	*exception = JSValueMakeString(ctx, exceptionString);
	JSStringRelease(exceptionString);
	return JSValueMakeUndefined(ctx);
}

JSValueRef JSCNamedNodeMap::getNamedItemNSCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {

	struct JSCNamedNodeMapPrivate* privData = (struct JSCNamedNodeMapPrivate*)JSObjectGetPrivate(thisObj);

	if (false) {
	} else if (argumentCount == 2 &&
	           JSValueIsString(ctx, arguments[0]) &&
	           JSValueIsString(ctx, arguments[1])) {
		JSStringRef stringReflocalNamespaceURI = JSValueToStringCopy(ctx, arguments[0], exception);
		size_t localNamespaceURIMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalNamespaceURI);
		char* localNamespaceURIBuffer = new char[localNamespaceURIMaxSize];
		JSStringGetUTF8CString(stringReflocalNamespaceURI, localNamespaceURIBuffer, localNamespaceURIMaxSize);
		std::string localNamespaceURI(localNamespaceURIBuffer);
		JSStringRelease(stringReflocalNamespaceURI);
		free(localNamespaceURIBuffer);

		JSStringRef stringReflocalLocalName = JSValueToStringCopy(ctx, arguments[1], exception);
		size_t localLocalNameMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalLocalName);
		char* localLocalNameBuffer = new char[localLocalNameMaxSize];
		JSStringGetUTF8CString(stringReflocalLocalName, localLocalNameBuffer, localLocalNameMaxSize);
		std::string localLocalName(localLocalNameBuffer);
		JSStringRelease(stringReflocalLocalName);
		free(localLocalNameBuffer);


		Arabica::DOM::Node<std::string>* retVal = new Arabica::DOM::Node<std::string>(privData->nativeObj->getNamedItemNS(localNamespaceURI, localLocalName));
		JSClassRef retClass = JSCNode::getTmpl();

		struct JSCNode::JSCNodePrivate* retPrivData = new JSCNode::JSCNodePrivate();
		retPrivData->dom = privData->dom;
		retPrivData->nativeObj = retVal;

		JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

		return retObj;

	}

	JSStringRef exceptionString = JSStringCreateWithUTF8CString("Parameter mismatch while calling getNamedItemNS");
	*exception = JSValueMakeString(ctx, exceptionString);
	JSStringRelease(exceptionString);
	return JSValueMakeUndefined(ctx);
}

JSValueRef JSCNamedNodeMap::setNamedItemNSCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {

	struct JSCNamedNodeMapPrivate* privData = (struct JSCNamedNodeMapPrivate*)JSObjectGetPrivate(thisObj);

	if (false) {
	} else if (argumentCount == 1 &&
	           JSValueIsObject(ctx, arguments[0]) && JSValueIsObjectOfClass(ctx, arguments[0], JSCNode::getTmpl())) {
		Arabica::DOM::Node<std::string>* localArg = ((struct JSCNode::JSCNodePrivate*)JSObjectGetPrivate(JSValueToObject(ctx, arguments[0], exception)))->nativeObj;

		Arabica::DOM::Node<std::string>* retVal = new Arabica::DOM::Node<std::string>(privData->nativeObj->setNamedItemNS(*localArg));
		JSClassRef retClass = JSCNode::getTmpl();

		struct JSCNode::JSCNodePrivate* retPrivData = new JSCNode::JSCNodePrivate();
		retPrivData->dom = privData->dom;
		retPrivData->nativeObj = retVal;

		JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

		return retObj;

	}

	JSStringRef exceptionString = JSStringCreateWithUTF8CString("Parameter mismatch while calling setNamedItemNS");
	*exception = JSValueMakeString(ctx, exceptionString);
	JSStringRelease(exceptionString);
	return JSValueMakeUndefined(ctx);
}

JSValueRef JSCNamedNodeMap::removeNamedItemNSCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {

	struct JSCNamedNodeMapPrivate* privData = (struct JSCNamedNodeMapPrivate*)JSObjectGetPrivate(thisObj);

	if (false) {
	} else if (argumentCount == 2 &&
	           JSValueIsString(ctx, arguments[0]) &&
	           JSValueIsString(ctx, arguments[1])) {
		JSStringRef stringReflocalNamespaceURI = JSValueToStringCopy(ctx, arguments[0], exception);
		size_t localNamespaceURIMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalNamespaceURI);
		char* localNamespaceURIBuffer = new char[localNamespaceURIMaxSize];
		JSStringGetUTF8CString(stringReflocalNamespaceURI, localNamespaceURIBuffer, localNamespaceURIMaxSize);
		std::string localNamespaceURI(localNamespaceURIBuffer);
		JSStringRelease(stringReflocalNamespaceURI);
		free(localNamespaceURIBuffer);

		JSStringRef stringReflocalLocalName = JSValueToStringCopy(ctx, arguments[1], exception);
		size_t localLocalNameMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalLocalName);
		char* localLocalNameBuffer = new char[localLocalNameMaxSize];
		JSStringGetUTF8CString(stringReflocalLocalName, localLocalNameBuffer, localLocalNameMaxSize);
		std::string localLocalName(localLocalNameBuffer);
		JSStringRelease(stringReflocalLocalName);
		free(localLocalNameBuffer);


		Arabica::DOM::Node<std::string>* retVal = new Arabica::DOM::Node<std::string>(privData->nativeObj->removeNamedItemNS(localNamespaceURI, localLocalName));
		JSClassRef retClass = JSCNode::getTmpl();

		struct JSCNode::JSCNodePrivate* retPrivData = new JSCNode::JSCNodePrivate();
		retPrivData->dom = privData->dom;
		retPrivData->nativeObj = retVal;

		JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

		return retObj;

	}

	JSStringRef exceptionString = JSStringCreateWithUTF8CString("Parameter mismatch while calling removeNamedItemNS");
	*exception = JSValueMakeString(ctx, exceptionString);
	JSStringRelease(exceptionString);
	return JSValueMakeUndefined(ctx);
}

}
}
