#include "JSCFloat64Array.h"

namespace Arabica {
namespace DOM {

JSClassRef JSCFloat64Array::Tmpl;

JSStaticValue JSCFloat64Array::staticValues[] = {
	{ "length", lengthAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },

	{ "BYTES_PER_ELEMENT", BYTES_PER_ELEMENTConstGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ 0, 0, 0, 0 }
};

JSStaticFunction JSCFloat64Array::staticFunctions[] = {
	{ "get", getCallback, kJSPropertyAttributeDontDelete },
	{ "set", setCallback, kJSPropertyAttributeDontDelete },
	{ "set", setCallback, kJSPropertyAttributeDontDelete },
	{ "set", setCallback, kJSPropertyAttributeDontDelete },
	{ "subarray", subarrayCallback, kJSPropertyAttributeDontDelete },
	{ 0, 0, 0 }
};

JSValueRef JSCFloat64Array::lengthAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCFloat64ArrayPrivate* privData = (struct JSCFloat64ArrayPrivate*)JSObjectGetPrivate(object);

	return JSValueMakeNumber(ctx, privData->nativeObj->getLength());
}

JSValueRef JSCFloat64Array::BYTES_PER_ELEMENTConstGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef *exception) {
	return JSValueMakeNumber(ctx, 8);
}

JSValueRef JSCFloat64Array::getCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 1) {
		std::string errorMsg = "Wrong number of arguments in get";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCFloat64ArrayPrivate* privData = (struct JSCFloat64ArrayPrivate*)JSObjectGetPrivate(thisObj);

	unsigned long localIndex = (unsigned long)JSValueToNumber(ctx, arguments[0], exception);

	double retVal = privData->nativeObj->get(localIndex);

	JSValueRef jscRetVal = JSValueMakeNumber(ctx, retVal);
	return jscRetVal;
}

JSValueRef JSCFloat64Array::setCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 2) {
		std::string errorMsg = "Wrong number of arguments in set";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCFloat64ArrayPrivate* privData = (struct JSCFloat64ArrayPrivate*)JSObjectGetPrivate(thisObj);

	unsigned long localIndex = (unsigned long)JSValueToNumber(ctx, arguments[0], exception);
	double localValue = (double)JSValueToNumber(ctx, arguments[1], exception);

	privData->nativeObj->set(localIndex, localValue);

	JSValueRef jscRetVal = JSValueMakeUndefined(ctx);
	return jscRetVal;
}

JSValueRef JSCFloat64Array::subarrayCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 2) {
		std::string errorMsg = "Wrong number of arguments in subarray";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCFloat64ArrayPrivate* privData = (struct JSCFloat64ArrayPrivate*)JSObjectGetPrivate(thisObj);

	long localStart = (long)JSValueToNumber(ctx, arguments[0], exception);
	long localEnd = (long)JSValueToNumber(ctx, arguments[1], exception);

	uscxml::Float64Array* retVal = new uscxml::Float64Array(privData->nativeObj->subarray(localStart, localEnd));
	JSClassRef retClass = JSCFloat64Array::getTmpl();

	struct JSCFloat64Array::JSCFloat64ArrayPrivate* retPrivData = new JSCFloat64Array::JSCFloat64ArrayPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

	return retObj;

}


}
}
