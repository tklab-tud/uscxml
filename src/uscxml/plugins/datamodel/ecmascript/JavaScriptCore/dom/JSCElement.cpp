#include "JSCElement.h"
#include "JSCNode.h"

namespace Arabica {
namespace DOM {


JSStaticValue JSCElement::staticValues[] = {
	{ "tagName", tagNameAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },

	{ 0, 0, 0, 0 }
};

JSStaticFunction JSCElement::staticFunctions[] = {
	{ "getAttribute", getAttributeCallback, kJSPropertyAttributeDontDelete },
	{ "setAttribute", setAttributeCallback, kJSPropertyAttributeDontDelete },
	{ "removeAttribute", removeAttributeCallback, kJSPropertyAttributeDontDelete },
	{ "getAttributeNode", getAttributeNodeCallback, kJSPropertyAttributeDontDelete },
	{ "setAttributeNode", setAttributeNodeCallback, kJSPropertyAttributeDontDelete },
	{ "removeAttributeNode", removeAttributeNodeCallback, kJSPropertyAttributeDontDelete },
	{ "getElementsByTagName", getElementsByTagNameCallback, kJSPropertyAttributeDontDelete },
	{ "getAttributeNS", getAttributeNSCallback, kJSPropertyAttributeDontDelete },
	{ "setAttributeNS", setAttributeNSCallback, kJSPropertyAttributeDontDelete },
	{ "removeAttributeNS", removeAttributeNSCallback, kJSPropertyAttributeDontDelete },
	{ "getAttributeNodeNS", getAttributeNodeNSCallback, kJSPropertyAttributeDontDelete },
	{ "setAttributeNodeNS", setAttributeNodeNSCallback, kJSPropertyAttributeDontDelete },
	{ "getElementsByTagNameNS", getElementsByTagNameNSCallback, kJSPropertyAttributeDontDelete },
	{ "hasAttribute", hasAttributeCallback, kJSPropertyAttributeDontDelete },
	{ "hasAttributeNS", hasAttributeNSCallback, kJSPropertyAttributeDontDelete },
	{ 0, 0, 0 }
};

JSValueRef JSCElement::tagNameAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCElementPrivate* privData = static_cast<JSCElement::JSCElementPrivate* >(JSObjectGetPrivate(thisObj));
	JSStringRef retString = JSStringCreateWithUTF8CString(privData->arabicaThis->getTagName().c_str());
	JSValueRef retObj = JSValueMakeString(ctx, retString);
	JSStringRelease(retString);
	return retObj;

}

}
}
