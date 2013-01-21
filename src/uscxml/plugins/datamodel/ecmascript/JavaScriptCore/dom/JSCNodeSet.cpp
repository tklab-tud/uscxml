#include "JSCNodeSet.h"

namespace Arabica {
namespace DOM {


JSStaticValue JSCNodeSet::staticValues[] = {
	{ "size", sizeAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "empty", emptyAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },

	{ 0, 0, 0, 0 }
};

JSStaticFunction JSCNodeSet::staticFunctions[] = {
	{ "toDocumentOrder", toDocumentOrderCallback, kJSPropertyAttributeDontDelete },
	{ 0, 0, 0 }
};

JSValueRef JSCNodeSet::sizeAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCNodeSetPrivate* privData = static_cast<JSCNodeSet::JSCNodeSetPrivate* >(JSObjectGetPrivate(thisObj));

	return JSValueMakeNumber(ctx, privData->arabicaThis->size());
}

JSValueRef JSCNodeSet::emptyAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCNodeSetPrivate* privData = static_cast<JSCNodeSet::JSCNodeSetPrivate* >(JSObjectGetPrivate(thisObj));

	return JSValueMakeBoolean(ctx, privData->arabicaThis->empty());
}

}
}
