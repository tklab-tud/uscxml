#include "JSCEntity.h"
#include "JSCNode.h"

namespace Arabica {
namespace DOM {


JSStaticValue JSCEntity::staticValues[] = {
	{ "publicId", publicIdAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "systemId", systemIdAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "notationName", notationNameAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },

	{ 0, 0, 0, 0 }
};

JSStaticFunction JSCEntity::staticFunctions[] = {
	{ 0, 0, 0 }
};

JSValueRef JSCEntity::publicIdAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCEntityPrivate* privData = static_cast<JSCEntity::JSCEntityPrivate* >(JSObjectGetPrivate(thisObj));
	JSStringRef retString = JSStringCreateWithUTF8CString(privData->arabicaThis->getPublicId().c_str());
	JSValueRef retObj = JSValueMakeString(ctx, retString);
	JSStringRelease(retString);
	return retObj;

}

JSValueRef JSCEntity::systemIdAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCEntityPrivate* privData = static_cast<JSCEntity::JSCEntityPrivate* >(JSObjectGetPrivate(thisObj));
	JSStringRef retString = JSStringCreateWithUTF8CString(privData->arabicaThis->getSystemId().c_str());
	JSValueRef retObj = JSValueMakeString(ctx, retString);
	JSStringRelease(retString);
	return retObj;

}

JSValueRef JSCEntity::notationNameAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCEntityPrivate* privData = static_cast<JSCEntity::JSCEntityPrivate* >(JSObjectGetPrivate(thisObj));
	JSStringRef retString = JSStringCreateWithUTF8CString(privData->arabicaThis->getNotationName().c_str());
	JSValueRef retObj = JSValueMakeString(ctx, retString);
	JSStringRelease(retString);
	return retObj;

}

}
}
