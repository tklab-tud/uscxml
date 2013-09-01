#include "JSCArrayBuffer.h"
#include "JSCArrayBufferView.h"
#include "JSCFloat32Array.h"

namespace Arabica {
namespace DOM {

JSClassRef JSCFloat32Array::Tmpl;

JSStaticValue JSCFloat32Array::staticValues[] = {
	{ "length", lengthAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },

	{ "BYTES_PER_ELEMENT", BYTES_PER_ELEMENTConstGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ 0, 0, 0, 0 }
};

JSStaticFunction JSCFloat32Array::staticFunctions[] = {
	{ "get", getCallback, kJSPropertyAttributeDontDelete },
	{ "set", setCallback, kJSPropertyAttributeDontDelete },
	{ "subarray", subarrayCallback, kJSPropertyAttributeDontDelete },
	{ 0, 0, 0 }
};

JSObjectRef JSCFloat32Array::jsConstructor(JSContextRef ctx, JSObjectRef constructor, size_t argumentCount, const JSValueRef arguments[], JSValueRef* exception) {
	uscxml::Float32Array* localInstance = NULL;

	if (false) {
	} else if (argumentCount == 3 &&
	           JSValueIsObject(ctx, arguments[0]) && JSValueIsObjectOfClass(ctx, arguments[0], JSCArrayBuffer::getTmpl()) &&
	           JSValueIsNumber(ctx, arguments[1]) &&
	           JSValueIsNumber(ctx, arguments[2])) {

		uscxml::ArrayBuffer* localBuffer = ((struct JSCArrayBuffer::JSCArrayBufferPrivate*)JSObjectGetPrivate(JSValueToObject(ctx, arguments[0], exception)))->nativeObj;
		unsigned long localByteOffset = (unsigned long)JSValueToNumber(ctx, arguments[1], exception);
		unsigned long localLength = (unsigned long)JSValueToNumber(ctx, arguments[2], exception);
		localInstance = new uscxml::Float32Array(localBuffer, localByteOffset, localLength);

	} else if (argumentCount == 2 &&
	           JSValueIsObject(ctx, arguments[0]) && JSValueIsObjectOfClass(ctx, arguments[0], JSCArrayBuffer::getTmpl()) &&
	           JSValueIsNumber(ctx, arguments[1])) {

		uscxml::ArrayBuffer* localBuffer = ((struct JSCArrayBuffer::JSCArrayBufferPrivate*)JSObjectGetPrivate(JSValueToObject(ctx, arguments[0], exception)))->nativeObj;
		unsigned long localByteOffset = (unsigned long)JSValueToNumber(ctx, arguments[1], exception);
		localInstance = new uscxml::Float32Array(localBuffer, localByteOffset);

	} else if (argumentCount == 1 &&
	           JSValueIsObject(ctx, arguments[0]) && JSValueIsObjectOfClass(ctx, arguments[0], JSCFloat32Array::getTmpl())) {

		uscxml::Float32Array* localArray = ((struct JSCFloat32Array::JSCFloat32ArrayPrivate*)JSObjectGetPrivate(JSValueToObject(ctx, arguments[0], exception)))->nativeObj;
		localInstance = new uscxml::Float32Array(localArray);

	} else if (argumentCount == 1 &&
	           JSValueIsObject(ctx, arguments[0]) && JSValueIsObjectOfClass(ctx, arguments[0], JSCArrayBuffer::getTmpl())) {

		uscxml::ArrayBuffer* localBuffer = ((struct JSCArrayBuffer::JSCArrayBufferPrivate*)JSObjectGetPrivate(JSValueToObject(ctx, arguments[0], exception)))->nativeObj;
		localInstance = new uscxml::Float32Array(localBuffer);

	} else if (argumentCount == 1 &&
	           JSValueIsNumber(ctx, arguments[0])) {

		unsigned long localLength = (unsigned long)JSValueToNumber(ctx, arguments[0], exception);
		localInstance = new uscxml::Float32Array(localLength);

	} else if (argumentCount == 1 &&
	           JSValueIsObject(ctx, arguments[0])) {


		std::vector<float> localArray;

		JSValueRef localArrayItem;
		unsigned int localArrayIndex = 0;
		while((localArrayItem = JSObjectGetPropertyAtIndex(ctx, JSValueToObject(ctx, arguments[0], exception), localArrayIndex, exception))) {
			if (JSValueIsUndefined(ctx, localArrayItem))
				break;
			if (JSValueIsNumber(ctx,localArrayItem))
				localArray.push_back(JSValueToNumber(ctx, localArrayItem, exception));
			localArrayIndex++;
		}
		localInstance = new uscxml::Float32Array(localArray);

	}
	if (!localInstance) {
		JSStringRef exceptionString = JSStringCreateWithUTF8CString("Parameter mismatch while calling constructor for Float32Array");
		*exception = JSValueMakeString(ctx, exceptionString);
		JSStringRelease(exceptionString);
		return (JSObjectRef)JSValueMakeNull(ctx);
	}

	JSClassRef retClass = JSCFloat32Array::getTmpl();

	struct JSCFloat32Array::JSCFloat32ArrayPrivate* retPrivData = new JSCFloat32Array::JSCFloat32ArrayPrivate();
	retPrivData->nativeObj = localInstance;

	JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);
	return retObj;
}

JSValueRef JSCFloat32Array::lengthAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCFloat32ArrayPrivate* privData = (struct JSCFloat32ArrayPrivate*)JSObjectGetPrivate(object);

	return JSValueMakeNumber(ctx, privData->nativeObj->getLength());
}

JSValueRef JSCFloat32Array::BYTES_PER_ELEMENTConstGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef *exception) {
	return JSValueMakeNumber(ctx, 4);
}


JSValueRef JSCFloat32Array::getCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {

	struct JSCFloat32ArrayPrivate* privData = (struct JSCFloat32ArrayPrivate*)JSObjectGetPrivate(thisObj);

	if (false) {
	} else if (argumentCount == 1 &&
	           JSValueIsNumber(ctx, arguments[0])) {
		unsigned long localIndex = (unsigned long)JSValueToNumber(ctx, arguments[0], exception);

		float retVal = privData->nativeObj->get(localIndex);

		JSValueRef jscRetVal = JSValueMakeNumber(ctx, retVal);
		return jscRetVal;
	}

	JSStringRef exceptionString = JSStringCreateWithUTF8CString("Parameter mismatch while calling get");
	*exception = JSValueMakeString(ctx, exceptionString);
	JSStringRelease(exceptionString);
	return JSValueMakeUndefined(ctx);
}

JSValueRef JSCFloat32Array::setCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {

	struct JSCFloat32ArrayPrivate* privData = (struct JSCFloat32ArrayPrivate*)JSObjectGetPrivate(thisObj);

	if (false) {
	} else if (argumentCount == 2 &&
	           JSValueIsObject(ctx, arguments[0]) && JSValueIsObjectOfClass(ctx, arguments[0], JSCFloat32Array::getTmpl()) &&
	           JSValueIsNumber(ctx, arguments[1])) {
		uscxml::Float32Array* localArray = ((struct JSCFloat32Array::JSCFloat32ArrayPrivate*)JSObjectGetPrivate(JSValueToObject(ctx, arguments[0], exception)))->nativeObj;
		unsigned long localOffset = (unsigned long)JSValueToNumber(ctx, arguments[1], exception);

		privData->nativeObj->set(localArray, localOffset);

		JSValueRef jscRetVal = JSValueMakeUndefined(ctx);
		return jscRetVal;
	} else if (argumentCount == 2 &&
	           JSValueIsNumber(ctx, arguments[0]) &&
	           JSValueIsNumber(ctx, arguments[1])) {
		unsigned long localIndex = (unsigned long)JSValueToNumber(ctx, arguments[0], exception);
		float localValue = (float)JSValueToNumber(ctx, arguments[1], exception);

		privData->nativeObj->set(localIndex, localValue);

		JSValueRef jscRetVal = JSValueMakeUndefined(ctx);
		return jscRetVal;
	} else if (argumentCount == 2 &&
	           JSValueIsObject(ctx, arguments[0]) &&
	           JSValueIsNumber(ctx, arguments[1])) {

		std::vector<float> localArray;

		JSValueRef localArrayItem;
		unsigned int localArrayIndex = 0;
		while((localArrayItem = JSObjectGetPropertyAtIndex(ctx, JSValueToObject(ctx, arguments[0], exception), localArrayIndex, exception))) {
			if (JSValueIsUndefined(ctx, localArrayItem))
				break;
			if (JSValueIsNumber(ctx,localArrayItem))
				localArray.push_back(JSValueToNumber(ctx, localArrayItem, exception));
			localArrayIndex++;
		}
		unsigned long localOffset = (unsigned long)JSValueToNumber(ctx, arguments[1], exception);

		privData->nativeObj->set(localArray, localOffset);

		JSValueRef jscRetVal = JSValueMakeUndefined(ctx);
		return jscRetVal;
	} else if (argumentCount == 1 &&
	           JSValueIsObject(ctx, arguments[0]) && JSValueIsObjectOfClass(ctx, arguments[0], JSCFloat32Array::getTmpl())) {
		uscxml::Float32Array* localArray = ((struct JSCFloat32Array::JSCFloat32ArrayPrivate*)JSObjectGetPrivate(JSValueToObject(ctx, arguments[0], exception)))->nativeObj;

		privData->nativeObj->set(localArray);

		JSValueRef jscRetVal = JSValueMakeUndefined(ctx);
		return jscRetVal;
	} else if (argumentCount == 1 &&
	           JSValueIsObject(ctx, arguments[0])) {

		std::vector<float> localArray;

		JSValueRef localArrayItem;
		unsigned int localArrayIndex = 0;
		while((localArrayItem = JSObjectGetPropertyAtIndex(ctx, JSValueToObject(ctx, arguments[0], exception), localArrayIndex, exception))) {
			if (JSValueIsUndefined(ctx, localArrayItem))
				break;
			if (JSValueIsNumber(ctx,localArrayItem))
				localArray.push_back(JSValueToNumber(ctx, localArrayItem, exception));
			localArrayIndex++;
		}

		privData->nativeObj->set(localArray);

		JSValueRef jscRetVal = JSValueMakeUndefined(ctx);
		return jscRetVal;
	}

	JSStringRef exceptionString = JSStringCreateWithUTF8CString("Parameter mismatch while calling set");
	*exception = JSValueMakeString(ctx, exceptionString);
	JSStringRelease(exceptionString);
	return JSValueMakeUndefined(ctx);
}

JSValueRef JSCFloat32Array::subarrayCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {

	struct JSCFloat32ArrayPrivate* privData = (struct JSCFloat32ArrayPrivate*)JSObjectGetPrivate(thisObj);

	if (false) {
	} else if (argumentCount == 2 &&
	           JSValueIsNumber(ctx, arguments[0]) &&
	           JSValueIsNumber(ctx, arguments[1])) {
		long localStart = (long)JSValueToNumber(ctx, arguments[0], exception);
		long localEnd = (long)JSValueToNumber(ctx, arguments[1], exception);

		uscxml::Float32Array* retVal = new uscxml::Float32Array(privData->nativeObj->subarray(localStart, localEnd));
		JSClassRef retClass = JSCFloat32Array::getTmpl();

		struct JSCFloat32Array::JSCFloat32ArrayPrivate* retPrivData = new JSCFloat32Array::JSCFloat32ArrayPrivate();
		retPrivData->dom = privData->dom;
		retPrivData->nativeObj = retVal;

		JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

		return retObj;

	}

	JSStringRef exceptionString = JSStringCreateWithUTF8CString("Parameter mismatch while calling subarray");
	*exception = JSValueMakeString(ctx, exceptionString);
	JSStringRelease(exceptionString);
	return JSValueMakeUndefined(ctx);
}

}
}
