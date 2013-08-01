#include "JSCDocumentType.h"
#include "JSCNamedNodeMap.h"
#include "JSCNode.h"

namespace Arabica {
namespace DOM {

JSClassRef JSCDocumentType::Tmpl;

JSStaticValue JSCDocumentType::staticValues[] = {
	{ "name", nameAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "entities", entitiesAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "notations", notationsAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "publicId", publicIdAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "systemId", systemIdAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "internalSubset", internalSubsetAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },

	{ 0, 0, 0, 0 }
};

JSStaticFunction JSCDocumentType::staticFunctions[] = {
	{ 0, 0, 0 }
};

JSValueRef JSCDocumentType::nameAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCDocumentTypePrivate* privData = (struct JSCDocumentTypePrivate*)JSObjectGetPrivate(object);

	JSStringRef stringRef = JSStringCreateWithUTF8CString(privData->nativeObj->getName().c_str());
	JSValueRef retVal = JSValueMakeString(ctx, stringRef);
	JSStringRelease(stringRef);
	return retVal;
}


JSValueRef JSCDocumentType::entitiesAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCDocumentTypePrivate* privData = (struct JSCDocumentTypePrivate*)JSObjectGetPrivate(object);


	Arabica::DOM::NamedNodeMap<std::string>* arabicaRet = new Arabica::DOM::NamedNodeMap<std::string>(privData->nativeObj->getEntities());

	JSClassRef arbaicaRetClass = JSCNamedNodeMap::getTmpl();

	struct JSCNamedNodeMap::JSCNamedNodeMapPrivate* retPrivData = new JSCNamedNodeMap::JSCNamedNodeMapPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = arabicaRet;

	JSObjectRef arbaicaRetObj = JSObjectMake(ctx, arbaicaRetClass, arabicaRet);
	return arbaicaRetObj;
}


JSValueRef JSCDocumentType::notationsAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCDocumentTypePrivate* privData = (struct JSCDocumentTypePrivate*)JSObjectGetPrivate(object);


	Arabica::DOM::NamedNodeMap<std::string>* arabicaRet = new Arabica::DOM::NamedNodeMap<std::string>(privData->nativeObj->getNotations());

	JSClassRef arbaicaRetClass = JSCNamedNodeMap::getTmpl();

	struct JSCNamedNodeMap::JSCNamedNodeMapPrivate* retPrivData = new JSCNamedNodeMap::JSCNamedNodeMapPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = arabicaRet;

	JSObjectRef arbaicaRetObj = JSObjectMake(ctx, arbaicaRetClass, arabicaRet);
	return arbaicaRetObj;
}


JSValueRef JSCDocumentType::publicIdAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCDocumentTypePrivate* privData = (struct JSCDocumentTypePrivate*)JSObjectGetPrivate(object);

	JSStringRef stringRef = JSStringCreateWithUTF8CString(privData->nativeObj->getPublicId().c_str());
	JSValueRef retVal = JSValueMakeString(ctx, stringRef);
	JSStringRelease(stringRef);
	return retVal;
}


JSValueRef JSCDocumentType::systemIdAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCDocumentTypePrivate* privData = (struct JSCDocumentTypePrivate*)JSObjectGetPrivate(object);

	JSStringRef stringRef = JSStringCreateWithUTF8CString(privData->nativeObj->getSystemId().c_str());
	JSValueRef retVal = JSValueMakeString(ctx, stringRef);
	JSStringRelease(stringRef);
	return retVal;
}


JSValueRef JSCDocumentType::internalSubsetAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCDocumentTypePrivate* privData = (struct JSCDocumentTypePrivate*)JSObjectGetPrivate(object);

	JSStringRef stringRef = JSStringCreateWithUTF8CString(privData->nativeObj->getInternalSubset().c_str());
	JSValueRef retVal = JSValueMakeString(ctx, stringRef);
	JSStringRelease(stringRef);
	return retVal;
}


}
}
