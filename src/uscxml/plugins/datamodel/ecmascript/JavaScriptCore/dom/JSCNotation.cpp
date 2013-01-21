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

JSValueRef JSCNotation::publicIdAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCNotationPrivate* privData = static_cast<JSCNotation::JSCNotationPrivate* >(JSObjectGetPrivate(thisObj));
	JSStringRef retString = JSStringCreateWithUTF8CString(privData->arabicaThis->getPublicId().c_str());
	JSValueRef retObj = JSValueMakeString(ctx, retString);
	JSStringRelease(retString);
	return retObj;

}

JSValueRef JSCNotation::systemIdAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCNotationPrivate* privData = static_cast<JSCNotation::JSCNotationPrivate* >(JSObjectGetPrivate(thisObj));
	JSStringRef retString = JSStringCreateWithUTF8CString(privData->arabicaThis->getSystemId().c_str());
	JSValueRef retObj = JSValueMakeString(ctx, retString);
	JSStringRelease(retString);
	return retObj;

}

}
}
