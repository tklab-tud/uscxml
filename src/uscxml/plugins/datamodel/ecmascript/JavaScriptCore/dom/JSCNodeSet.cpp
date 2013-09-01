#include "JSCNodeSet.h"

namespace Arabica {
namespace DOM {

JSClassRef JSCNodeSet::Tmpl;

JSStaticValue JSCNodeSet::staticValues[] = {
	{ "size", sizeAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "empty", emptyAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },

	{ 0, 0, 0, 0 }
};

JSStaticFunction JSCNodeSet::staticFunctions[] = {
	{ "toDocumentOrder", toDocumentOrderCallback, kJSPropertyAttributeDontDelete },
	{ 0, 0, 0 }
};

JSValueRef JSCNodeSet::sizeAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCNodeSetPrivate* privData = (struct JSCNodeSetPrivate*)JSObjectGetPrivate(object);

	return JSValueMakeNumber(ctx, privData->nativeObj->size());
}


JSValueRef JSCNodeSet::emptyAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCNodeSetPrivate* privData = (struct JSCNodeSetPrivate*)JSObjectGetPrivate(object);

	return JSValueMakeBoolean(ctx, privData->nativeObj->empty());
}


JSValueRef JSCNodeSet::toDocumentOrderCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {

	struct JSCNodeSetPrivate* privData = (struct JSCNodeSetPrivate*)JSObjectGetPrivate(thisObj);

	if (false) {
	} else if (argumentCount == 0) {

		privData->nativeObj->to_document_order();

		JSValueRef jscRetVal = JSValueMakeUndefined(ctx);
		return jscRetVal;
	}

	JSStringRef exceptionString = JSStringCreateWithUTF8CString("Parameter mismatch while calling toDocumentOrder");
	*exception = JSValueMakeString(ctx, exceptionString);
	JSStringRelease(exceptionString);
	return JSValueMakeUndefined(ctx);
}

}
}
