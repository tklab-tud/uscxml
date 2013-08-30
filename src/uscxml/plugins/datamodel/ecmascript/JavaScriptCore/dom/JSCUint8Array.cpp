#include "JSCUint8Array.h"

namespace Arabica {
namespace DOM {

JSClassRef JSCUint8Array::Tmpl;

JSStaticValue JSCUint8Array::staticValues[] = {
	{ "length", lengthAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },

	{ "BYTES_PER_ELEMENT", BYTES_PER_ELEMENTConstGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ 0, 0, 0, 0 }
};

JSStaticFunction JSCUint8Array::staticFunctions[] = {
	{ "get", getCallback, kJSPropertyAttributeDontDelete },
	{ "set", setCallback, kJSPropertyAttributeDontDelete },
	{ "set", setCallback, kJSPropertyAttributeDontDelete },
	{ "set", setCallback, kJSPropertyAttributeDontDelete },
	{ "subarray", subarrayCallback, kJSPropertyAttributeDontDelete },
	{ 0, 0, 0 }
};

JSValueRef JSCUint8Array::lengthAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCUint8ArrayPrivate* privData = (struct JSCUint8ArrayPrivate*)JSObjectGetPrivate(object);

	return JSValueMakeNumber(ctx, privData->nativeObj->getLength());
}

JSValueRef JSCUint8Array::BYTES_PER_ELEMENTConstGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef *exception) {
	return JSValueMakeNumber(ctx, 1);
}

JSValueRef JSCUint8Array::getCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 1) {
		std::string errorMsg = "Wrong number of arguments in get";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCUint8ArrayPrivate* privData = (struct JSCUint8ArrayPrivate*)JSObjectGetPrivate(thisObj);

	unsigned long localIndex = (unsigned long)JSValueToNumber(ctx, arguments[0], exception);

	char retVal = privData->nativeObj->get(localIndex);

	JSValueRef jscRetVal = JSValueMakeNumber(ctx, retVal);
	return jscRetVal;
}

JSValueRef JSCUint8Array::setCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 2) {
		std::string errorMsg = "Wrong number of arguments in set";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCUint8ArrayPrivate* privData = (struct JSCUint8ArrayPrivate*)JSObjectGetPrivate(thisObj);

	unsigned long localIndex = (unsigned long)JSValueToNumber(ctx, arguments[0], exception);
	unsigned char localValue = (char)JSValueToNumber(ctx, arguments[1], exception);

	privData->nativeObj->set(localIndex, localValue);

	JSValueRef jscRetVal = JSValueMakeUndefined(ctx);
	return jscRetVal;
}

JSValueRef JSCUint8Array::subarrayCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 2) {
		std::string errorMsg = "Wrong number of arguments in subarray";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCUint8ArrayPrivate* privData = (struct JSCUint8ArrayPrivate*)JSObjectGetPrivate(thisObj);

	long localStart = (long)JSValueToNumber(ctx, arguments[0], exception);
	long localEnd = (long)JSValueToNumber(ctx, arguments[1], exception);

	uscxml::Uint8Array* retVal = new uscxml::Uint8Array(privData->nativeObj->subarray(localStart, localEnd));
	JSClassRef retClass = JSCUint8Array::getTmpl();

	struct JSCUint8Array::JSCUint8ArrayPrivate* retPrivData = new JSCUint8Array::JSCUint8ArrayPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

	return retObj;

}


}
}
