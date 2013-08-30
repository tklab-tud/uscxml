#include "JSCDataView.h"

namespace Arabica {
namespace DOM {

JSClassRef JSCDataView::Tmpl;

JSStaticValue JSCDataView::staticValues[] = {

	{ 0, 0, 0, 0 }
};

JSStaticFunction JSCDataView::staticFunctions[] = {
	{ "getInt8", getInt8Callback, kJSPropertyAttributeDontDelete },
	{ "getUint8", getUint8Callback, kJSPropertyAttributeDontDelete },
	{ "getInt16", getInt16Callback, kJSPropertyAttributeDontDelete },
	{ "getUint16", getUint16Callback, kJSPropertyAttributeDontDelete },
	{ "getInt32", getInt32Callback, kJSPropertyAttributeDontDelete },
	{ "getUint32", getUint32Callback, kJSPropertyAttributeDontDelete },
	{ "getFloat32", getFloat32Callback, kJSPropertyAttributeDontDelete },
	{ "getFloat64", getFloat64Callback, kJSPropertyAttributeDontDelete },
	{ "setInt8", setInt8Callback, kJSPropertyAttributeDontDelete },
	{ "setUint8", setUint8Callback, kJSPropertyAttributeDontDelete },
	{ "setInt16", setInt16Callback, kJSPropertyAttributeDontDelete },
	{ "setUint16", setUint16Callback, kJSPropertyAttributeDontDelete },
	{ "setInt32", setInt32Callback, kJSPropertyAttributeDontDelete },
	{ "setUint32", setUint32Callback, kJSPropertyAttributeDontDelete },
	{ "setFloat32", setFloat32Callback, kJSPropertyAttributeDontDelete },
	{ "setFloat64", setFloat64Callback, kJSPropertyAttributeDontDelete },
	{ 0, 0, 0 }
};
JSValueRef JSCDataView::getInt8Callback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 1) {
		std::string errorMsg = "Wrong number of arguments in getInt8";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCDataViewPrivate* privData = (struct JSCDataViewPrivate*)JSObjectGetPrivate(thisObj);

	unsigned long localByteOffset = (unsigned long)JSValueToNumber(ctx, arguments[0], exception);

	char retVal = privData->nativeObj->getInt8(localByteOffset);

	JSValueRef jscRetVal = JSValueMakeNumber(ctx, retVal);
	return jscRetVal;
}

JSValueRef JSCDataView::getUint8Callback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 1) {
		std::string errorMsg = "Wrong number of arguments in getUint8";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCDataViewPrivate* privData = (struct JSCDataViewPrivate*)JSObjectGetPrivate(thisObj);

	unsigned long localByteOffset = (unsigned long)JSValueToNumber(ctx, arguments[0], exception);

	char retVal = privData->nativeObj->getUint8(localByteOffset);

	JSValueRef jscRetVal = JSValueMakeNumber(ctx, retVal);
	return jscRetVal;
}

JSValueRef JSCDataView::getInt16Callback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 2) {
		std::string errorMsg = "Wrong number of arguments in getInt16";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCDataViewPrivate* privData = (struct JSCDataViewPrivate*)JSObjectGetPrivate(thisObj);

	unsigned long localByteOffset = (unsigned long)JSValueToNumber(ctx, arguments[0], exception);
	bool localLittleEndian = JSValueToBoolean(ctx, arguments[1]);

	short retVal = privData->nativeObj->getInt16(localByteOffset, localLittleEndian);

	JSValueRef jscRetVal = JSValueMakeNumber(ctx, retVal);
	return jscRetVal;
}

JSValueRef JSCDataView::getUint16Callback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 2) {
		std::string errorMsg = "Wrong number of arguments in getUint16";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCDataViewPrivate* privData = (struct JSCDataViewPrivate*)JSObjectGetPrivate(thisObj);

	unsigned long localByteOffset = (unsigned long)JSValueToNumber(ctx, arguments[0], exception);
	bool localLittleEndian = JSValueToBoolean(ctx, arguments[1]);

	unsigned short retVal = privData->nativeObj->getUint16(localByteOffset, localLittleEndian);

	JSValueRef jscRetVal = JSValueMakeNumber(ctx, retVal);
	return jscRetVal;
}

JSValueRef JSCDataView::getInt32Callback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 2) {
		std::string errorMsg = "Wrong number of arguments in getInt32";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCDataViewPrivate* privData = (struct JSCDataViewPrivate*)JSObjectGetPrivate(thisObj);

	unsigned long localByteOffset = (unsigned long)JSValueToNumber(ctx, arguments[0], exception);
	bool localLittleEndian = JSValueToBoolean(ctx, arguments[1]);

	long retVal = privData->nativeObj->getInt32(localByteOffset, localLittleEndian);

	JSValueRef jscRetVal = JSValueMakeNumber(ctx, retVal);
	return jscRetVal;
}

JSValueRef JSCDataView::getUint32Callback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 2) {
		std::string errorMsg = "Wrong number of arguments in getUint32";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCDataViewPrivate* privData = (struct JSCDataViewPrivate*)JSObjectGetPrivate(thisObj);

	unsigned long localByteOffset = (unsigned long)JSValueToNumber(ctx, arguments[0], exception);
	bool localLittleEndian = JSValueToBoolean(ctx, arguments[1]);

	unsigned long retVal = privData->nativeObj->getUint32(localByteOffset, localLittleEndian);

	JSValueRef jscRetVal = JSValueMakeNumber(ctx, retVal);
	return jscRetVal;
}

JSValueRef JSCDataView::getFloat32Callback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 2) {
		std::string errorMsg = "Wrong number of arguments in getFloat32";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCDataViewPrivate* privData = (struct JSCDataViewPrivate*)JSObjectGetPrivate(thisObj);

	unsigned long localByteOffset = (unsigned long)JSValueToNumber(ctx, arguments[0], exception);
	bool localLittleEndian = JSValueToBoolean(ctx, arguments[1]);

	float retVal = privData->nativeObj->getFloat32(localByteOffset, localLittleEndian);

	JSValueRef jscRetVal = JSValueMakeNumber(ctx, retVal);
	return jscRetVal;
}

JSValueRef JSCDataView::getFloat64Callback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 2) {
		std::string errorMsg = "Wrong number of arguments in getFloat64";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCDataViewPrivate* privData = (struct JSCDataViewPrivate*)JSObjectGetPrivate(thisObj);

	unsigned long localByteOffset = (unsigned long)JSValueToNumber(ctx, arguments[0], exception);
	bool localLittleEndian = JSValueToBoolean(ctx, arguments[1]);

	double retVal = privData->nativeObj->getFloat64(localByteOffset, localLittleEndian);

	JSValueRef jscRetVal = JSValueMakeNumber(ctx, retVal);
	return jscRetVal;
}

JSValueRef JSCDataView::setInt8Callback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 2) {
		std::string errorMsg = "Wrong number of arguments in setInt8";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCDataViewPrivate* privData = (struct JSCDataViewPrivate*)JSObjectGetPrivate(thisObj);

	unsigned long localByteOffset = (unsigned long)JSValueToNumber(ctx, arguments[0], exception);
	char localValue = (char)JSValueToNumber(ctx, arguments[1], exception);

	privData->nativeObj->setInt8(localByteOffset, localValue);

	JSValueRef jscRetVal = JSValueMakeUndefined(ctx);
	return jscRetVal;
}

JSValueRef JSCDataView::setUint8Callback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 2) {
		std::string errorMsg = "Wrong number of arguments in setUint8";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCDataViewPrivate* privData = (struct JSCDataViewPrivate*)JSObjectGetPrivate(thisObj);

	unsigned long localByteOffset = (unsigned long)JSValueToNumber(ctx, arguments[0], exception);
	unsigned char localValue = (char)JSValueToNumber(ctx, arguments[1], exception);

	privData->nativeObj->setUint8(localByteOffset, localValue);

	JSValueRef jscRetVal = JSValueMakeUndefined(ctx);
	return jscRetVal;
}

JSValueRef JSCDataView::setInt16Callback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 3) {
		std::string errorMsg = "Wrong number of arguments in setInt16";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCDataViewPrivate* privData = (struct JSCDataViewPrivate*)JSObjectGetPrivate(thisObj);

	unsigned long localByteOffset = (unsigned long)JSValueToNumber(ctx, arguments[0], exception);
	short localValue = (short)JSValueToNumber(ctx, arguments[1], exception);
	bool localLittleEndian = JSValueToBoolean(ctx, arguments[2]);

	privData->nativeObj->setInt16(localByteOffset, localValue, localLittleEndian);

	JSValueRef jscRetVal = JSValueMakeUndefined(ctx);
	return jscRetVal;
}

JSValueRef JSCDataView::setUint16Callback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 3) {
		std::string errorMsg = "Wrong number of arguments in setUint16";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCDataViewPrivate* privData = (struct JSCDataViewPrivate*)JSObjectGetPrivate(thisObj);

	unsigned long localByteOffset = (unsigned long)JSValueToNumber(ctx, arguments[0], exception);
	unsigned short localValue = (unsigned short)JSValueToNumber(ctx, arguments[1], exception);
	bool localLittleEndian = JSValueToBoolean(ctx, arguments[2]);

	privData->nativeObj->setUint16(localByteOffset, localValue, localLittleEndian);

	JSValueRef jscRetVal = JSValueMakeUndefined(ctx);
	return jscRetVal;
}

JSValueRef JSCDataView::setInt32Callback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 3) {
		std::string errorMsg = "Wrong number of arguments in setInt32";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCDataViewPrivate* privData = (struct JSCDataViewPrivate*)JSObjectGetPrivate(thisObj);

	unsigned long localByteOffset = (unsigned long)JSValueToNumber(ctx, arguments[0], exception);
	long localValue = (long)JSValueToNumber(ctx, arguments[1], exception);
	bool localLittleEndian = JSValueToBoolean(ctx, arguments[2]);

	privData->nativeObj->setInt32(localByteOffset, localValue, localLittleEndian);

	JSValueRef jscRetVal = JSValueMakeUndefined(ctx);
	return jscRetVal;
}

JSValueRef JSCDataView::setUint32Callback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 3) {
		std::string errorMsg = "Wrong number of arguments in setUint32";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCDataViewPrivate* privData = (struct JSCDataViewPrivate*)JSObjectGetPrivate(thisObj);

	unsigned long localByteOffset = (unsigned long)JSValueToNumber(ctx, arguments[0], exception);
	unsigned long localValue = (unsigned long)JSValueToNumber(ctx, arguments[1], exception);
	bool localLittleEndian = JSValueToBoolean(ctx, arguments[2]);

	privData->nativeObj->setUint32(localByteOffset, localValue, localLittleEndian);

	JSValueRef jscRetVal = JSValueMakeUndefined(ctx);
	return jscRetVal;
}

JSValueRef JSCDataView::setFloat32Callback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 3) {
		std::string errorMsg = "Wrong number of arguments in setFloat32";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCDataViewPrivate* privData = (struct JSCDataViewPrivate*)JSObjectGetPrivate(thisObj);

	unsigned long localByteOffset = (unsigned long)JSValueToNumber(ctx, arguments[0], exception);
	float localValue = (float)JSValueToNumber(ctx, arguments[1], exception);
	bool localLittleEndian = JSValueToBoolean(ctx, arguments[2]);

	privData->nativeObj->setFloat32(localByteOffset, localValue, localLittleEndian);

	JSValueRef jscRetVal = JSValueMakeUndefined(ctx);
	return jscRetVal;
}

JSValueRef JSCDataView::setFloat64Callback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 3) {
		std::string errorMsg = "Wrong number of arguments in setFloat64";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCDataViewPrivate* privData = (struct JSCDataViewPrivate*)JSObjectGetPrivate(thisObj);

	unsigned long localByteOffset = (unsigned long)JSValueToNumber(ctx, arguments[0], exception);
	double localValue = (double)JSValueToNumber(ctx, arguments[1], exception);
	bool localLittleEndian = JSValueToBoolean(ctx, arguments[2]);

	privData->nativeObj->setFloat64(localByteOffset, localValue, localLittleEndian);

	JSValueRef jscRetVal = JSValueMakeUndefined(ctx);
	return jscRetVal;
}


}
}
