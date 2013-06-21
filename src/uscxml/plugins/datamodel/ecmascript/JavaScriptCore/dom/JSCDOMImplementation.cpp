#include "JSCDOMImplementation.h"
#include "JSCDocument.h"
#include "JSCDocumentType.h"

namespace Arabica {
namespace DOM {

JSClassRef JSCDOMImplementation::Tmpl;

JSStaticValue JSCDOMImplementation::staticValues[] = {

	{ 0, 0, 0, 0 }
};

JSStaticFunction JSCDOMImplementation::staticFunctions[] = {
	{ "hasFeature", hasFeatureCallback, kJSPropertyAttributeDontDelete },
	{ "createDocumentType", createDocumentTypeCallback, kJSPropertyAttributeDontDelete },
	{ "createDocument", createDocumentCallback, kJSPropertyAttributeDontDelete },
	{ 0, 0, 0 }
};
JSValueRef JSCDOMImplementation::hasFeatureCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 2) {
		std::string errorMsg = "Wrong number of arguments in hasFeature";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCDOMImplementationPrivate* privData = (struct JSCDOMImplementationPrivate*)JSObjectGetPrivate(thisObj);

	JSStringRef stringReflocalFeature = JSValueToStringCopy(ctx, arguments[0], exception);
	size_t localFeatureMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalFeature);
	char* localFeatureBuffer = new char[localFeatureMaxSize];
	JSStringGetUTF8CString(stringReflocalFeature, localFeatureBuffer, sizeof(localFeatureBuffer));
	std::string localFeature(localFeatureBuffer, localFeatureMaxSize);
	free(localFeatureBuffer);

	JSStringRef stringReflocalVersion = JSValueToStringCopy(ctx, arguments[1], exception);
	size_t localVersionMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalVersion);
	char* localVersionBuffer = new char[localVersionMaxSize];
	JSStringGetUTF8CString(stringReflocalVersion, localVersionBuffer, sizeof(localVersionBuffer));
	std::string localVersion(localVersionBuffer, localVersionMaxSize);
	free(localVersionBuffer);


	bool retVal = privData->nativeObj->hasFeature(localFeature, localVersion);

	JSValueRef jscRetVal = JSValueMakeBoolean(ctx, retVal);
	return jscRetVal;
}

JSValueRef JSCDOMImplementation::createDocumentTypeCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 3) {
		std::string errorMsg = "Wrong number of arguments in createDocumentType";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCDOMImplementationPrivate* privData = (struct JSCDOMImplementationPrivate*)JSObjectGetPrivate(thisObj);

	JSStringRef stringReflocalQualifiedName = JSValueToStringCopy(ctx, arguments[0], exception);
	size_t localQualifiedNameMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalQualifiedName);
	char* localQualifiedNameBuffer = new char[localQualifiedNameMaxSize];
	JSStringGetUTF8CString(stringReflocalQualifiedName, localQualifiedNameBuffer, sizeof(localQualifiedNameBuffer));
	std::string localQualifiedName(localQualifiedNameBuffer, localQualifiedNameMaxSize);
	free(localQualifiedNameBuffer);

	JSStringRef stringReflocalPublicId = JSValueToStringCopy(ctx, arguments[1], exception);
	size_t localPublicIdMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalPublicId);
	char* localPublicIdBuffer = new char[localPublicIdMaxSize];
	JSStringGetUTF8CString(stringReflocalPublicId, localPublicIdBuffer, sizeof(localPublicIdBuffer));
	std::string localPublicId(localPublicIdBuffer, localPublicIdMaxSize);
	free(localPublicIdBuffer);

	JSStringRef stringReflocalSystemId = JSValueToStringCopy(ctx, arguments[2], exception);
	size_t localSystemIdMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalSystemId);
	char* localSystemIdBuffer = new char[localSystemIdMaxSize];
	JSStringGetUTF8CString(stringReflocalSystemId, localSystemIdBuffer, sizeof(localSystemIdBuffer));
	std::string localSystemId(localSystemIdBuffer, localSystemIdMaxSize);
	free(localSystemIdBuffer);


	Arabica::DOM::DocumentType<std::string>* retVal = new Arabica::DOM::DocumentType<std::string>(privData->nativeObj->createDocumentType(localQualifiedName, localPublicId, localSystemId));
	JSClassRef retClass = JSCDocumentType::getTmpl();

	struct JSCDocumentType::JSCDocumentTypePrivate* retPrivData = new JSCDocumentType::JSCDocumentTypePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

	return retObj;

}

JSValueRef JSCDOMImplementation::createDocumentCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 3) {
		std::string errorMsg = "Wrong number of arguments in createDocument";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCDOMImplementationPrivate* privData = (struct JSCDOMImplementationPrivate*)JSObjectGetPrivate(thisObj);

	JSStringRef stringReflocalNamespaceURI = JSValueToStringCopy(ctx, arguments[0], exception);
	size_t localNamespaceURIMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalNamespaceURI);
	char* localNamespaceURIBuffer = new char[localNamespaceURIMaxSize];
	JSStringGetUTF8CString(stringReflocalNamespaceURI, localNamespaceURIBuffer, sizeof(localNamespaceURIBuffer));
	std::string localNamespaceURI(localNamespaceURIBuffer, localNamespaceURIMaxSize);
	free(localNamespaceURIBuffer);

	JSStringRef stringReflocalQualifiedName = JSValueToStringCopy(ctx, arguments[1], exception);
	size_t localQualifiedNameMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalQualifiedName);
	char* localQualifiedNameBuffer = new char[localQualifiedNameMaxSize];
	JSStringGetUTF8CString(stringReflocalQualifiedName, localQualifiedNameBuffer, sizeof(localQualifiedNameBuffer));
	std::string localQualifiedName(localQualifiedNameBuffer, localQualifiedNameMaxSize);
	free(localQualifiedNameBuffer);

	Arabica::DOM::DocumentType<std::string>* localDoctype = ((struct JSCDocumentType::JSCDocumentTypePrivate*)JSObjectGetPrivate(thisObj))->nativeObj;

	Arabica::DOM::Document<std::string>* retVal = new Arabica::DOM::Document<std::string>(privData->nativeObj->createDocument(localNamespaceURI, localQualifiedName, *localDoctype));
	JSClassRef retClass = JSCDocument::getTmpl();

	struct JSCDocument::JSCDocumentPrivate* retPrivData = new JSCDocument::JSCDocumentPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

	return retObj;

}


}
}
