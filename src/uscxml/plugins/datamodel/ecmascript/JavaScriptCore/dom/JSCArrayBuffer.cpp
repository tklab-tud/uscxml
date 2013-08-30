#include "JSCArrayBuffer.h"

namespace Arabica {
namespace DOM {

JSClassRef JSCArrayBuffer::Tmpl;

JSStaticValue JSCArrayBuffer::staticValues[] = {
	{ "byteLength", byteLengthAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },

	{ 0, 0, 0, 0 }
};

JSStaticFunction JSCArrayBuffer::staticFunctions[] = {
	{ "slice", sliceCallback, kJSPropertyAttributeDontDelete },
	{ "isView", isViewCallback, kJSPropertyAttributeDontDelete },
	{ 0, 0, 0 }
};

JSValueRef JSCArrayBuffer::byteLengthAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCArrayBufferPrivate* privData = (struct JSCArrayBufferPrivate*)JSObjectGetPrivate(object);

	return JSValueMakeNumber(ctx, privData->nativeObj->getByteLength());
}

JSValueRef JSCArrayBuffer::sliceCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 2) {
		std::string errorMsg = "Wrong number of arguments in slice";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCArrayBufferPrivate* privData = (struct JSCArrayBufferPrivate*)JSObjectGetPrivate(thisObj);

	long localBegin = (long)JSValueToNumber(ctx, arguments[0], exception);
	long localEnd = (long)JSValueToNumber(ctx, arguments[1], exception);

	uscxml::ArrayBuffer* retVal = new uscxml::ArrayBuffer(privData->nativeObj->slice(localBegin, localEnd));
	JSClassRef retClass = JSCArrayBuffer::getTmpl();

	struct JSCArrayBuffer::JSCArrayBufferPrivate* retPrivData = new JSCArrayBuffer::JSCArrayBufferPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

	return retObj;

}

JSValueRef JSCArrayBuffer::isViewCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 1) {
		std::string errorMsg = "Wrong number of arguments in isView";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCArrayBufferPrivate* privData = (struct JSCArrayBufferPrivate*)JSObjectGetPrivate(thisObj);

	void* localValue = JSObjectGetPrivate(JSValueToObject(ctx, arguments[0], exception));

	bool retVal = privData->nativeObj->isView(localValue);

	JSValueRef jscRetVal = JSValueMakeBoolean(ctx, retVal);
	return jscRetVal;
}


}
}
