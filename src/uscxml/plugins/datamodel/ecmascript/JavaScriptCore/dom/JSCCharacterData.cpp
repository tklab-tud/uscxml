#include "JSCCharacterData.h"
#include "JSCNode.h"

namespace Arabica {
namespace DOM {

JSClassRef JSCCharacterData::Tmpl;

JSStaticValue JSCCharacterData::staticValues[] = {
	{ "data", dataAttrGetter, dataAttrSetter, kJSPropertyAttributeDontDelete },
	{ "length", lengthAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },

	{ 0, 0, 0, 0 }
};

JSStaticFunction JSCCharacterData::staticFunctions[] = {
	{ "substringData", substringDataCallback, kJSPropertyAttributeDontDelete },
	{ "appendData", appendDataCallback, kJSPropertyAttributeDontDelete },
	{ "insertData", insertDataCallback, kJSPropertyAttributeDontDelete },
	{ "deleteData", deleteDataCallback, kJSPropertyAttributeDontDelete },
	{ "replaceData", replaceDataCallback, kJSPropertyAttributeDontDelete },
	{ 0, 0, 0 }
};

JSValueRef JSCCharacterData::dataAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCCharacterDataPrivate* privData = (struct JSCCharacterDataPrivate*)JSObjectGetPrivate(object);

	JSStringRef stringRef = JSStringCreateWithUTF8CString(privData->nativeObj->getData().c_str());
	JSValueRef retVal = JSValueMakeString(ctx, stringRef);
	JSStringRelease(stringRef);
	return retVal;
}


bool JSCCharacterData::dataAttrSetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef value, JSValueRef* exception) {
	struct JSCCharacterDataPrivate* privData = (struct JSCCharacterDataPrivate*)JSObjectGetPrivate(thisObj);

	JSStringRef stringReflocalData = JSValueToStringCopy(ctx, value, exception);
	size_t localDataMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalData);
	char* localDataBuffer = new char[localDataMaxSize];
	JSStringGetUTF8CString(stringReflocalData, localDataBuffer, localDataMaxSize);
	std::string localData(localDataBuffer);
	JSStringRelease(stringReflocalData);
	free(localDataBuffer);

	privData->nativeObj->setData(localData);
	return true;
}

JSValueRef JSCCharacterData::lengthAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCCharacterDataPrivate* privData = (struct JSCCharacterDataPrivate*)JSObjectGetPrivate(object);

	return JSValueMakeNumber(ctx, privData->nativeObj->getLength());
}

JSValueRef JSCCharacterData::substringDataCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 2) {
		std::string errorMsg = "Wrong number of arguments in substringData";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCCharacterDataPrivate* privData = (struct JSCCharacterDataPrivate*)JSObjectGetPrivate(thisObj);

	unsigned long localOffset = (unsigned long)JSValueToNumber(ctx, arguments[0], exception);
	unsigned long localCount = (unsigned long)JSValueToNumber(ctx, arguments[1], exception);

	std::string retVal = privData->nativeObj->substringData(localOffset, localCount);

	JSStringRef jscString = JSStringCreateWithUTF8CString(retVal.c_str());
	JSValueRef jscRetVal = JSValueMakeString(ctx, jscString);
	JSStringRelease(jscString);
	return jscRetVal;
}

JSValueRef JSCCharacterData::appendDataCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 1) {
		std::string errorMsg = "Wrong number of arguments in appendData";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCCharacterDataPrivate* privData = (struct JSCCharacterDataPrivate*)JSObjectGetPrivate(thisObj);

	JSStringRef stringReflocalArg = JSValueToStringCopy(ctx, arguments[0], exception);
	size_t localArgMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalArg);
	char* localArgBuffer = new char[localArgMaxSize];
	JSStringGetUTF8CString(stringReflocalArg, localArgBuffer, localArgMaxSize);
	std::string localArg(localArgBuffer);
	JSStringRelease(stringReflocalArg);
	free(localArgBuffer);


	privData->nativeObj->appendData(localArg);

	JSValueRef jscRetVal = JSValueMakeUndefined(ctx);
	return jscRetVal;
}

JSValueRef JSCCharacterData::insertDataCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 2) {
		std::string errorMsg = "Wrong number of arguments in insertData";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCCharacterDataPrivate* privData = (struct JSCCharacterDataPrivate*)JSObjectGetPrivate(thisObj);

	unsigned long localOffset = (unsigned long)JSValueToNumber(ctx, arguments[0], exception);
	JSStringRef stringReflocalArg = JSValueToStringCopy(ctx, arguments[1], exception);
	size_t localArgMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalArg);
	char* localArgBuffer = new char[localArgMaxSize];
	JSStringGetUTF8CString(stringReflocalArg, localArgBuffer, localArgMaxSize);
	std::string localArg(localArgBuffer);
	JSStringRelease(stringReflocalArg);
	free(localArgBuffer);


	privData->nativeObj->insertData(localOffset, localArg);

	JSValueRef jscRetVal = JSValueMakeUndefined(ctx);
	return jscRetVal;
}

JSValueRef JSCCharacterData::deleteDataCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 2) {
		std::string errorMsg = "Wrong number of arguments in deleteData";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCCharacterDataPrivate* privData = (struct JSCCharacterDataPrivate*)JSObjectGetPrivate(thisObj);

	unsigned long localOffset = (unsigned long)JSValueToNumber(ctx, arguments[0], exception);
	unsigned long localCount = (unsigned long)JSValueToNumber(ctx, arguments[1], exception);

	privData->nativeObj->deleteData(localOffset, localCount);

	JSValueRef jscRetVal = JSValueMakeUndefined(ctx);
	return jscRetVal;
}

JSValueRef JSCCharacterData::replaceDataCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 3) {
		std::string errorMsg = "Wrong number of arguments in replaceData";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCCharacterDataPrivate* privData = (struct JSCCharacterDataPrivate*)JSObjectGetPrivate(thisObj);

	unsigned long localOffset = (unsigned long)JSValueToNumber(ctx, arguments[0], exception);
	unsigned long localCount = (unsigned long)JSValueToNumber(ctx, arguments[1], exception);
	JSStringRef stringReflocalArg = JSValueToStringCopy(ctx, arguments[2], exception);
	size_t localArgMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalArg);
	char* localArgBuffer = new char[localArgMaxSize];
	JSStringGetUTF8CString(stringReflocalArg, localArgBuffer, localArgMaxSize);
	std::string localArg(localArgBuffer);
	JSStringRelease(stringReflocalArg);
	free(localArgBuffer);


	privData->nativeObj->replaceData(localOffset, localCount, localArg);

	JSValueRef jscRetVal = JSValueMakeUndefined(ctx);
	return jscRetVal;
}


}
}
