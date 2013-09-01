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

JSObjectRef JSCArrayBuffer::jsConstructor(JSContextRef ctx, JSObjectRef constructor, size_t argumentCount, const JSValueRef arguments[], JSValueRef* exception) {
	uscxml::ArrayBuffer* localInstance = NULL;

	if (false) {
	} else if (argumentCount == 1 &&
	           JSValueIsNumber(ctx, arguments[0])) {

		unsigned long localLength = (unsigned long)JSValueToNumber(ctx, arguments[0], exception);
		localInstance = new uscxml::ArrayBuffer(localLength);

	}
	if (!localInstance) {
		JSStringRef exceptionString = JSStringCreateWithUTF8CString("Parameter mismatch while calling constructor for ArrayBuffer");
		*exception = JSValueMakeString(ctx, exceptionString);
		JSStringRelease(exceptionString);
		return (JSObjectRef)JSValueMakeNull(ctx);
	}

	JSClassRef retClass = JSCArrayBuffer::getTmpl();

	struct JSCArrayBuffer::JSCArrayBufferPrivate* retPrivData = new JSCArrayBuffer::JSCArrayBufferPrivate();
	retPrivData->nativeObj = localInstance;

	JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);
	return retObj;
}

JSValueRef JSCArrayBuffer::byteLengthAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCArrayBufferPrivate* privData = (struct JSCArrayBufferPrivate*)JSObjectGetPrivate(object);

	return JSValueMakeNumber(ctx, privData->nativeObj->getByteLength());
}


JSValueRef JSCArrayBuffer::sliceCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {

	struct JSCArrayBufferPrivate* privData = (struct JSCArrayBufferPrivate*)JSObjectGetPrivate(thisObj);

	if (false) {
	} else if (argumentCount == 2 &&
	           JSValueIsNumber(ctx, arguments[0]) &&
	           JSValueIsNumber(ctx, arguments[1])) {
		long localBegin = (long)JSValueToNumber(ctx, arguments[0], exception);
		long localEnd = (long)JSValueToNumber(ctx, arguments[1], exception);

		uscxml::ArrayBuffer* retVal = new uscxml::ArrayBuffer(privData->nativeObj->slice(localBegin, localEnd));
		JSClassRef retClass = JSCArrayBuffer::getTmpl();

		struct JSCArrayBuffer::JSCArrayBufferPrivate* retPrivData = new JSCArrayBuffer::JSCArrayBufferPrivate();
		retPrivData->dom = privData->dom;
		retPrivData->nativeObj = retVal;

		JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

		return retObj;

	} else if (argumentCount == 1 &&
	           JSValueIsNumber(ctx, arguments[0])) {
		long localBegin = (long)JSValueToNumber(ctx, arguments[0], exception);

		uscxml::ArrayBuffer* retVal = new uscxml::ArrayBuffer(privData->nativeObj->slice(localBegin));
		JSClassRef retClass = JSCArrayBuffer::getTmpl();

		struct JSCArrayBuffer::JSCArrayBufferPrivate* retPrivData = new JSCArrayBuffer::JSCArrayBufferPrivate();
		retPrivData->dom = privData->dom;
		retPrivData->nativeObj = retVal;

		JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

		return retObj;

	}

	JSStringRef exceptionString = JSStringCreateWithUTF8CString("Parameter mismatch while calling slice");
	*exception = JSValueMakeString(ctx, exceptionString);
	JSStringRelease(exceptionString);
	return JSValueMakeUndefined(ctx);
}

JSValueRef JSCArrayBuffer::isViewCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {

	struct JSCArrayBufferPrivate* privData = (struct JSCArrayBufferPrivate*)JSObjectGetPrivate(thisObj);

	if (false) {
	} else if (argumentCount == 1 &&
	           true) {
		void* localValue = JSObjectGetPrivate(JSValueToObject(ctx, arguments[0], exception));

		bool retVal = privData->nativeObj->isView(localValue);

		JSValueRef jscRetVal = JSValueMakeBoolean(ctx, retVal);
		return jscRetVal;
	}

	JSStringRef exceptionString = JSStringCreateWithUTF8CString("Parameter mismatch while calling isView");
	*exception = JSValueMakeString(ctx, exceptionString);
	JSStringRelease(exceptionString);
	return JSValueMakeUndefined(ctx);
}

}
}
