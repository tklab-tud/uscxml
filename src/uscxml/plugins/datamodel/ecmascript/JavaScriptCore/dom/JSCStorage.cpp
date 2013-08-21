#include "JSCStorage.h"

namespace Arabica {
namespace DOM {

JSClassRef JSCStorage::Tmpl;

JSStaticValue JSCStorage::staticValues[] = {
	{ "length", lengthAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },

	{ 0, 0, 0, 0 }
};

JSStaticFunction JSCStorage::staticFunctions[] = {
	{ "key", keyCallback, kJSPropertyAttributeDontDelete },
	{ "getItem", getItemCallback, kJSPropertyAttributeDontDelete },
	{ "setItem", setItemCallback, kJSPropertyAttributeDontDelete },
	{ "removeItem", removeItemCallback, kJSPropertyAttributeDontDelete },
	{ "clear", clearCallback, kJSPropertyAttributeDontDelete },
	{ 0, 0, 0 }
};

JSValueRef JSCStorage::lengthAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCStoragePrivate* privData = (struct JSCStoragePrivate*)JSObjectGetPrivate(object);

	return JSValueMakeNumber(ctx, privData->nativeObj->getLength());
}

JSValueRef JSCStorage::keyCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 1) {
		std::string errorMsg = "Wrong number of arguments in key";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCStoragePrivate* privData = (struct JSCStoragePrivate*)JSObjectGetPrivate(thisObj);

	unsigned long localIndex = (unsigned long)JSValueToNumber(ctx, arguments[0], exception);

	std::string retVal = privData->nativeObj->key(localIndex);

	JSStringRef jscString = JSStringCreateWithUTF8CString(retVal.c_str());
	JSValueRef jscRetVal = JSValueMakeString(ctx, jscString);
	JSStringRelease(jscString);
	return jscRetVal;
}

JSValueRef JSCStorage::getItemCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 1) {
		std::string errorMsg = "Wrong number of arguments in getItem";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCStoragePrivate* privData = (struct JSCStoragePrivate*)JSObjectGetPrivate(thisObj);

	JSStringRef stringReflocalKey = JSValueToStringCopy(ctx, arguments[0], exception);
	size_t localKeyMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalKey);
	char* localKeyBuffer = new char[localKeyMaxSize];
	JSStringGetUTF8CString(stringReflocalKey, localKeyBuffer, localKeyMaxSize);
	std::string localKey(localKeyBuffer);
	JSStringRelease(stringReflocalKey);
	free(localKeyBuffer);


	std::string retVal = privData->nativeObj->getItem(localKey);

	JSStringRef jscString = JSStringCreateWithUTF8CString(retVal.c_str());
	JSValueRef jscRetVal = JSValueMakeString(ctx, jscString);
	JSStringRelease(jscString);
	return jscRetVal;
}

JSValueRef JSCStorage::setItemCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 2) {
		std::string errorMsg = "Wrong number of arguments in setItem";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCStoragePrivate* privData = (struct JSCStoragePrivate*)JSObjectGetPrivate(thisObj);

	JSStringRef stringReflocalKey = JSValueToStringCopy(ctx, arguments[0], exception);
	size_t localKeyMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalKey);
	char* localKeyBuffer = new char[localKeyMaxSize];
	JSStringGetUTF8CString(stringReflocalKey, localKeyBuffer, localKeyMaxSize);
	std::string localKey(localKeyBuffer);
	JSStringRelease(stringReflocalKey);
	free(localKeyBuffer);

	JSStringRef stringReflocalValue = JSValueToStringCopy(ctx, arguments[1], exception);
	size_t localValueMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalValue);
	char* localValueBuffer = new char[localValueMaxSize];
	JSStringGetUTF8CString(stringReflocalValue, localValueBuffer, localValueMaxSize);
	std::string localValue(localValueBuffer);
	JSStringRelease(stringReflocalValue);
	free(localValueBuffer);


	privData->nativeObj->setItem(localKey, localValue);

	JSValueRef jscRetVal = JSValueMakeUndefined(ctx);
	return jscRetVal;
}

JSValueRef JSCStorage::removeItemCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 1) {
		std::string errorMsg = "Wrong number of arguments in removeItem";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCStoragePrivate* privData = (struct JSCStoragePrivate*)JSObjectGetPrivate(thisObj);

	JSStringRef stringReflocalKey = JSValueToStringCopy(ctx, arguments[0], exception);
	size_t localKeyMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalKey);
	char* localKeyBuffer = new char[localKeyMaxSize];
	JSStringGetUTF8CString(stringReflocalKey, localKeyBuffer, localKeyMaxSize);
	std::string localKey(localKeyBuffer);
	JSStringRelease(stringReflocalKey);
	free(localKeyBuffer);


	privData->nativeObj->removeItem(localKey);

	JSValueRef jscRetVal = JSValueMakeUndefined(ctx);
	return jscRetVal;
}

JSValueRef JSCStorage::clearCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {

	struct JSCStoragePrivate* privData = (struct JSCStoragePrivate*)JSObjectGetPrivate(thisObj);


	privData->nativeObj->clear();

	JSValueRef jscRetVal = JSValueMakeUndefined(ctx);
	return jscRetVal;
}


}
}
