#include "JSCNodeList.h"

namespace Arabica {
namespace DOM {


JSStaticValue JSCNodeList::staticValues[] = {
	{ "length", lengthAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },

	{ 0, 0, 0, 0 }
};

JSStaticFunction JSCNodeList::staticFunctions[] = {
	{ "item", itemCallback, kJSPropertyAttributeDontDelete },
	{ 0, 0, 0 }
};

JSValueRef JSCNodeList::lengthAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCNodeListPrivate* privData = static_cast<JSCNodeList::JSCNodeListPrivate* >(JSObjectGetPrivate(thisObj));

	return JSValueMakeNumber(ctx, privData->arabicaThis->getLength());
}

}
}
