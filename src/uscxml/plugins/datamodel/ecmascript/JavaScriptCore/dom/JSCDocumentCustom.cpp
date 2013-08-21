#include "JSCDocument.h"
#include "JSCStorage.h"
#include "JSCXPathResult.h"
#include "JSCNode.h"
#include <XPath/XPath.hpp>

namespace Arabica {
namespace DOM {

JSValueRef JSCDocument::localStorageCustomAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCDocumentPrivate* privData = (struct JSCDocumentPrivate*)JSObjectGetPrivate(object);

	if (!privData->dom->storage) {
		return JSValueMakeUndefined(ctx);
	}

	JSClassRef retClass = JSCStorage::getTmpl();
	struct JSCStorage::JSCStoragePrivate* retPrivData = new JSCStorage::JSCStoragePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retPrivData->dom->storage;

	JSObjectRef arbaicaRetObj = JSObjectMake(ctx, retClass, retPrivData);
	return arbaicaRetObj;

}


JSValueRef JSCDocument::evaluateCustomCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef object, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	struct JSCDocumentPrivate* privData = (struct JSCDocumentPrivate*)JSObjectGetPrivate(object);

	if (!privData->dom || !privData->dom->xpath) return JSValueMakeUndefined(ctx);
	if (argumentCount < 1) {
		std::string errorMsg = "Wrong number of arguments in evaluate";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString = JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return JSValueMakeUndefined(ctx);
	}

	// make sure first argument is a string
	if (!JSValueIsString(ctx, arguments[0])) {
		std::string errorMsg = "Expected xpath expression as first argument";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString = JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return JSValueMakeUndefined(ctx);
	}

	JSStringRef stringReflocalXPath = JSValueToStringCopy(ctx, arguments[0], NULL);
	size_t localXPathMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalXPath);
	char* localXPathBuffer = new char[localXPathMaxSize];
	JSStringGetUTF8CString(stringReflocalXPath, localXPathBuffer, localXPathMaxSize);
	std::string localXPath(localXPathBuffer);
	JSStringRelease(stringReflocalXPath);
	free(localXPathBuffer);

	JSClassRef arbaicaRetClass = JSCXPathResult::getTmpl();

	XPath::XPathValue<std::string>* retVal;

	try {
		if (argumentCount > 1) {
			// make sure second argument is a node
			if (!JSValueIsObject(ctx, arguments[1])) {
				std::string errorMsg = "Second argument is not of type node";
				JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
				JSValueRef exceptionString = JSValueMakeString(ctx, string);
				JSStringRelease(string);
				*exception = JSValueToObject(ctx, exceptionString, NULL);
				return JSValueMakeUndefined(ctx);
			}

			Arabica::DOM::Node<std::string>* localContextNode = (Arabica::DOM::Node<std::string>*)JSObjectGetPrivate(JSValueToObject(ctx, arguments[1], NULL));
			retVal = new XPath::XPathValue<std::string>(privData->dom->xpath->evaluate(localXPath, *localContextNode));
		} else {
			retVal = new XPath::XPathValue<std::string>(privData->dom->xpath->evaluate(localXPath, *privData->nativeObj));
		}
	} catch (std::runtime_error e) {
		std::cout << e.what() << std::endl;
		return JSValueMakeUndefined(ctx);
	}

	struct JSCXPathResult::JSCXPathResultPrivate* retPrivData = new JSCXPathResult::JSCXPathResultPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	JSObjectRef arbaicaRetObj = JSObjectMake(ctx, arbaicaRetClass, retPrivData);
	return arbaicaRetObj;

#if 0
	if (args.Length() < 1)
		throw V8Exception("Wrong number of arguments in evaluate");
//  if (!((V8Node::hasInstance(args[1])) && (V8XPathResult::hasInstance(args[3]))))
//    throw V8Exception("Parameter mismatch while calling evaluate");

	v8::Local<v8::Object> self = args.Holder();
	V8DocumentPrivate* privData = V8DOM::toClassPtr<V8DocumentPrivate >(self->GetInternalField(0));

	v8::String::AsciiValue localExpression(args[0]);

	XPath::XPathValue<std::string>* retVal;
	if (args.Length() > 1) {
		Arabica::DOM::Node<std::string>* localContextNode = V8DOM::toClassPtr<Arabica::DOM::Node<std::string> >(args[1]->ToObject()->GetInternalField(0));
		retVal = new XPath::XPathValue<std::string>(privData->dom->xpath->evaluate(*localExpression, *localContextNode));
	} else {
		retVal = new XPath::XPathValue<std::string>(privData->dom->xpath->evaluate(*localExpression, *privData->nativeObj));
	}

	v8::Handle<v8::Function> retCtor = V8XPathResult::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

	V8XPathResult::V8XPathResultPrivate* retPrivData = new V8XPathResult::V8XPathResultPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));

	retObj.MakeWeak(0, V8XPathResult::jsDestructor);
	return retObj;
#endif
}

}
}