#include "JSCUint32Array.h"

namespace Arabica {
namespace DOM {

JSClassRef JSCUint32Array::Tmpl;

JSStaticValue JSCUint32Array::staticValues[] = {
	{ "length", lengthAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },

	{ "BYTES_PER_ELEMENT", BYTES_PER_ELEMENTConstGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ 0, 0, 0, 0 }
};

JSStaticFunction JSCUint32Array::staticFunctions[] = {
	{ "get", getCallback, kJSPropertyAttributeDontDelete },
	{ "set", setCallback, kJSPropertyAttributeDontDelete },
	{ "set", setCallback, kJSPropertyAttributeDontDelete },
	{ "set", setCallback, kJSPropertyAttributeDontDelete },
	{ "subarray", subarrayCallback, kJSPropertyAttributeDontDelete },
	{ 0, 0, 0 }
};

JSValueRef JSCUint32Array::lengthAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCUint32ArrayPrivate* privData = (struct JSCUint32ArrayPrivate*)JSObjectGetPrivate(object);

	return JSValueMakeNumber(ctx, privData->nativeObj->getLength());
}

JSValueRef JSCUint32Array::BYTES_PER_ELEMENTConstGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef *exception) {
	return JSValueMakeNumber(ctx, 4);
}

JSValueRef JSCUint32Array::getCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 1) {
		std::string errorMsg = "Wrong number of arguments in get";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCUint32ArrayPrivate* privData = (struct JSCUint32ArrayPrivate*)JSObjectGetPrivate(thisObj);

	unsigned long localIndex = (unsigned long)JSValueToNumber(ctx, arguments[0], exception);

	unsigned long retVal = privData->nativeObj->get(localIndex);

	JSValueRef jscRetVal = JSValueMakeNumber(ctx, retVal);
	return jscRetVal;
}

JSValueRef JSCUint32Array::setCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 2) {
		std::string errorMsg = "Wrong number of arguments in set";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCUint32ArrayPrivate* privData = (struct JSCUint32ArrayPrivate*)JSObjectGetPrivate(thisObj);

	unsigned long localIndex = (unsigned long)JSValueToNumber(ctx, arguments[0], exception);
	unsigned long localValue = (unsigned long)JSValueToNumber(ctx, arguments[1], exception);

	privData->nativeObj->set(localIndex, localValue);

	JSValueRef jscRetVal = JSValueMakeUndefined(ctx);
	return jscRetVal;
}

JSValueRef JSCUint32Array::subarrayCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 2) {
		std::string errorMsg = "Wrong number of arguments in subarray";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCUint32ArrayPrivate* privData = (struct JSCUint32ArrayPrivate*)JSObjectGetPrivate(thisObj);

	long localStart = (long)JSValueToNumber(ctx, arguments[0], exception);
	long localEnd = (long)JSValueToNumber(ctx, arguments[1], exception);

	uscxml::Uint32Array* retVal = new uscxml::Uint32Array(privData->nativeObj->subarray(localStart, localEnd));
	JSClassRef retClass = JSCUint32Array::getTmpl();

	struct JSCUint32Array::JSCUint32ArrayPrivate* retPrivData = new JSCUint32Array::JSCUint32ArrayPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

	return retObj;

}


}
}
