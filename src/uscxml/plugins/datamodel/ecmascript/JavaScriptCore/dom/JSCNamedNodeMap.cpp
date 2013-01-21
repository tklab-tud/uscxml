#include "JSCNamedNodeMap.h"

namespace Arabica {
namespace DOM {


JSStaticValue JSCNamedNodeMap::staticValues[] = {
	{ "length", lengthAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },

	{ 0, 0, 0, 0 }
};

JSStaticFunction JSCNamedNodeMap::staticFunctions[] = {
	{ "getNamedItem", getNamedItemCallback, kJSPropertyAttributeDontDelete },
	{ "setNamedItem", setNamedItemCallback, kJSPropertyAttributeDontDelete },
	{ "removeNamedItem", removeNamedItemCallback, kJSPropertyAttributeDontDelete },
	{ "item", itemCallback, kJSPropertyAttributeDontDelete },
	{ "getNamedItemNS", getNamedItemNSCallback, kJSPropertyAttributeDontDelete },
	{ "setNamedItemNS", setNamedItemNSCallback, kJSPropertyAttributeDontDelete },
	{ "removeNamedItemNS", removeNamedItemNSCallback, kJSPropertyAttributeDontDelete },
	{ 0, 0, 0 }
};

JSValueRef JSCNamedNodeMap::lengthAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCNamedNodeMapPrivate* privData = static_cast<JSCNamedNodeMap::JSCNamedNodeMapPrivate* >(JSObjectGetPrivate(thisObj));

	return JSValueMakeNumber(ctx, privData->arabicaThis->getLength());
}

}
}
