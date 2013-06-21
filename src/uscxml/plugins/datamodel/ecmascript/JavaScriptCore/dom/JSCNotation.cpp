#include "JSCNode.h"
#include "JSCNotation.h"

namespace Arabica {
namespace DOM {


JSStaticValue JSCNotation::staticValues[] = {
	{ "publicId", publicIdAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "systemId", systemIdAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },

	{ 0, 0, 0, 0 }
};

JSStaticFunction JSCNotation::staticFunctions[] = {
	{ 0, 0, 0 }
};

JSValueRef JSCNotation::publicIdAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCNotationPrivate* privData = (struct JSCNotationPrivate*)JSObjectGetPrivate(object);
	JSStringRef stringRef = JSStringCreateWithUTF8CString(privData->nativeObj->getPublicId().c_str());
	return JSValueMakeString(ctx, stringRef);
}


JSValueRef JSCNotation::systemIdAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCNotationPrivate* privData = (struct JSCNotationPrivate*)JSObjectGetPrivate(object);
	JSStringRef stringRef = JSStringCreateWithUTF8CString(privData->nativeObj->getSystemId().c_str());
	return JSValueMakeString(ctx, stringRef);
}


}
}
