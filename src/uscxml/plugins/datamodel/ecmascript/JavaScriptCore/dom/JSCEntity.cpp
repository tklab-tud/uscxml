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

JSValueRef JSCEntity::publicIdAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCEntityPrivate* privData = (struct JSCEntityPrivate*)JSObjectGetPrivate(object);
	JSStringRef stringRef = JSStringCreateWithUTF8CString(privData->nativeObj->getPublicId().c_str());
	return JSValueMakeString(ctx, stringRef);
}


JSValueRef JSCEntity::systemIdAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCEntityPrivate* privData = (struct JSCEntityPrivate*)JSObjectGetPrivate(object);
	JSStringRef stringRef = JSStringCreateWithUTF8CString(privData->nativeObj->getSystemId().c_str());
	return JSValueMakeString(ctx, stringRef);
}


JSValueRef JSCEntity::notationNameAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCEntityPrivate* privData = (struct JSCEntityPrivate*)JSObjectGetPrivate(object);
	JSStringRef stringRef = JSStringCreateWithUTF8CString(privData->nativeObj->getNotationName().c_str());
	return JSValueMakeString(ctx, stringRef);
}


}
}
