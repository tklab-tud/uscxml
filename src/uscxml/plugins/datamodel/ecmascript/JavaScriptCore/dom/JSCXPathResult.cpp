#include "JSCXPathResult.h"

namespace Arabica {
namespace DOM {


JSStaticValue JSCXPathResult::staticValues[] = {
	{ "numberValue", numberValueAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "stringValue", stringValueAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "booleanValue", booleanValueAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "singleNodeValue", singleNodeValueCustomAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },

	{ 0, 0, 0, 0 }
};

JSStaticFunction JSCXPathResult::staticFunctions[] = {
	{ "asNodeSet", asNodeSetCallback, kJSPropertyAttributeDontDelete },
	{ "asBool", asBoolCallback, kJSPropertyAttributeDontDelete },
	{ "asString", asStringCallback, kJSPropertyAttributeDontDelete },
	{ "asNumber", asNumberCallback, kJSPropertyAttributeDontDelete },
	{ 0, 0, 0 }
};

JSValueRef JSCXPathResult::numberValueAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCXPathResultPrivate* privData = static_cast<JSCXPathResult::JSCXPathResultPrivate* >(JSObjectGetPrivate(thisObj));

	return JSValueMakeNumber(ctx, privData->arabicaThis->asNumber());
}

JSValueRef JSCXPathResult::stringValueAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCXPathResultPrivate* privData = static_cast<JSCXPathResult::JSCXPathResultPrivate* >(JSObjectGetPrivate(thisObj));
	JSStringRef retString = JSStringCreateWithUTF8CString(privData->arabicaThis->asString().c_str());
	JSValueRef retObj = JSValueMakeString(ctx, retString);
	JSStringRelease(retString);
	return retObj;

}

JSValueRef JSCXPathResult::booleanValueAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCXPathResultPrivate* privData = static_cast<JSCXPathResult::JSCXPathResultPrivate* >(JSObjectGetPrivate(thisObj));

	return JSValueMakeBoolean(ctx, privData->arabicaThis->asBool());
}

}
}
