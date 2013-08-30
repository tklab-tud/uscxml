#include "JSCUint8ClampedArray.h"

namespace Arabica {
namespace DOM {

JSClassRef JSCUint8ClampedArray::Tmpl;

JSStaticValue JSCUint8ClampedArray::staticValues[] = {
	{ "length", lengthAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },

	{ "BYTES_PER_ELEMENT", BYTES_PER_ELEMENTConstGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ 0, 0, 0, 0 }
};

JSStaticFunction JSCUint8ClampedArray::staticFunctions[] = {
	{ "get", getCallback, kJSPropertyAttributeDontDelete },
	{ "set", setCallback, kJSPropertyAttributeDontDelete },
	{ "set", setCallback, kJSPropertyAttributeDontDelete },
	{ "set", setCallback, kJSPropertyAttributeDontDelete },
	{ "subarray", subarrayCallback, kJSPropertyAttributeDontDelete },
	{ 0, 0, 0 }
};

JSValueRef JSCUint8ClampedArray::lengthAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCUint8ClampedArrayPrivate* privData = (struct JSCUint8ClampedArrayPrivate*)JSObjectGetPrivate(object);

	return JSValueMakeNumber(ctx, privData->nativeObj->getLength());
}

JSValueRef JSCUint8ClampedArray::BYTES_PER_ELEMENTConstGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef *exception) {
	return JSValueMakeNumber(ctx, 1);
}

JSValueRef JSCUint8ClampedArray::getCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 1) {
		std::string errorMsg = "Wrong number of arguments in get";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCUint8ClampedArrayPrivate* privData = (struct JSCUint8ClampedArrayPrivate*)JSObjectGetPrivate(thisObj);

	unsigned long localIndex = (unsigned long)JSValueToNumber(ctx, arguments[0], exception);

	char retVal = privData->nativeObj->get(localIndex);

	JSValueRef jscRetVal = JSValueMakeNumber(ctx, retVal);
	return jscRetVal;
}

JSValueRef JSCUint8ClampedArray::setCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 2) {
		std::string errorMsg = "Wrong number of arguments in set";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCUint8ClampedArrayPrivate* privData = (struct JSCUint8ClampedArrayPrivate*)JSObjectGetPrivate(thisObj);

	unsigned long localIndex = (unsigned long)JSValueToNumber(ctx, arguments[0], exception);
	unsigned char localValue = (char)JSValueToNumber(ctx, arguments[1], exception);

	privData->nativeObj->set(localIndex, localValue);

	JSValueRef jscRetVal = JSValueMakeUndefined(ctx);
	return jscRetVal;
}

JSValueRef JSCUint8ClampedArray::subarrayCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 2) {
		std::string errorMsg = "Wrong number of arguments in subarray";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCUint8ClampedArrayPrivate* privData = (struct JSCUint8ClampedArrayPrivate*)JSObjectGetPrivate(thisObj);

	long localStart = (long)JSValueToNumber(ctx, arguments[0], exception);
	long localEnd = (long)JSValueToNumber(ctx, arguments[1], exception);

	uscxml::Uint8ClampedArray* retVal = new uscxml::Uint8ClampedArray(privData->nativeObj->subarray(localStart, localEnd));
	JSClassRef retClass = JSCUint8ClampedArray::getTmpl();

	struct JSCUint8ClampedArray::JSCUint8ClampedArrayPrivate* retPrivData = new JSCUint8ClampedArray::JSCUint8ClampedArrayPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

	return retObj;

}


}
}
