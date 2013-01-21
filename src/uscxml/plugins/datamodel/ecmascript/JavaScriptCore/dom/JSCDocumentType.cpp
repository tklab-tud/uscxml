#include "JSCDocumentType.h"
#include "JSCNamedNodeMap.h"
#include "JSCNode.h"

namespace Arabica {
namespace DOM {


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

JSValueRef JSCDocumentType::nameAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCDocumentTypePrivate* privData = static_cast<JSCDocumentType::JSCDocumentTypePrivate* >(JSObjectGetPrivate(thisObj));
	JSStringRef retString = JSStringCreateWithUTF8CString(privData->arabicaThis->getName().c_str());
	JSValueRef retObj = JSValueMakeString(ctx, retString);
	JSStringRelease(retString);
	return retObj;

}

JSValueRef JSCDocumentType::entitiesAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCDocumentTypePrivate* privData = static_cast<JSCDocumentType::JSCDocumentTypePrivate* >(JSObjectGetPrivate(thisObj));
	Arabica::DOM::NamedNodeMap<std::string>* arbaicaRet = new Arabica::DOM::NamedNodeMap<std::string>(privData->arabicaThis->getEntities());

	struct JSCNamedNodeMap::JSCNamedNodeMapPrivate* retPrivData = new JSCNamedNodeMap::JSCNamedNodeMapPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->arabicaThis = arbaicaRet;

	JSObjectRef arbaicaRetObj = JSObjectMake(ctx, JSCNamedNodeMap::getTmpl(), retPrivData);
	return arbaicaRetObj;

}

JSValueRef JSCDocumentType::notationsAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCDocumentTypePrivate* privData = static_cast<JSCDocumentType::JSCDocumentTypePrivate* >(JSObjectGetPrivate(thisObj));
	Arabica::DOM::NamedNodeMap<std::string>* arbaicaRet = new Arabica::DOM::NamedNodeMap<std::string>(privData->arabicaThis->getNotations());

	struct JSCNamedNodeMap::JSCNamedNodeMapPrivate* retPrivData = new JSCNamedNodeMap::JSCNamedNodeMapPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->arabicaThis = arbaicaRet;

	JSObjectRef arbaicaRetObj = JSObjectMake(ctx, JSCNamedNodeMap::getTmpl(), retPrivData);
	return arbaicaRetObj;

}

JSValueRef JSCDocumentType::publicIdAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCDocumentTypePrivate* privData = static_cast<JSCDocumentType::JSCDocumentTypePrivate* >(JSObjectGetPrivate(thisObj));
	JSStringRef retString = JSStringCreateWithUTF8CString(privData->arabicaThis->getPublicId().c_str());
	JSValueRef retObj = JSValueMakeString(ctx, retString);
	JSStringRelease(retString);
	return retObj;

}

JSValueRef JSCDocumentType::systemIdAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCDocumentTypePrivate* privData = static_cast<JSCDocumentType::JSCDocumentTypePrivate* >(JSObjectGetPrivate(thisObj));
	JSStringRef retString = JSStringCreateWithUTF8CString(privData->arabicaThis->getSystemId().c_str());
	JSValueRef retObj = JSValueMakeString(ctx, retString);
	JSStringRelease(retString);
	return retObj;

}

JSValueRef JSCDocumentType::internalSubsetAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCDocumentTypePrivate* privData = static_cast<JSCDocumentType::JSCDocumentTypePrivate* >(JSObjectGetPrivate(thisObj));
	JSStringRef retString = JSStringCreateWithUTF8CString(privData->arabicaThis->getInternalSubset().c_str());
	JSValueRef retObj = JSValueMakeString(ctx, retString);
	JSStringRelease(retString);
	return retObj;

}

}
}
