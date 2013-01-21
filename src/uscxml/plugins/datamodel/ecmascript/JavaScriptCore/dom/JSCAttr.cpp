#include "JSCAttr.h"
#include "JSCElement.h"
#include "JSCNode.h"

namespace Arabica {
namespace DOM {


JSStaticValue JSCAttr::staticValues[] = {
	{ "name", nameAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "specified", specifiedAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "value", valueAttrGetter, valueAttrSetter, kJSPropertyAttributeDontDelete },
	{ "ownerElement", ownerElementAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },

	{ 0, 0, 0, 0 }
};

JSStaticFunction JSCAttr::staticFunctions[] = {
	{ 0, 0, 0 }
};

JSValueRef JSCAttr::nameAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCAttrPrivate* privData = static_cast<JSCAttr::JSCAttrPrivate* >(JSObjectGetPrivate(thisObj));
	JSStringRef retString = JSStringCreateWithUTF8CString(privData->arabicaThis->getName().c_str());
	JSValueRef retObj = JSValueMakeString(ctx, retString);
	JSStringRelease(retString);
	return retObj;

}

JSValueRef JSCAttr::specifiedAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCAttrPrivate* privData = static_cast<JSCAttr::JSCAttrPrivate* >(JSObjectGetPrivate(thisObj));

	return JSValueMakeBoolean(ctx, privData->arabicaThis->getSpecified());
}

JSValueRef JSCAttr::valueAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCAttrPrivate* privData = static_cast<JSCAttr::JSCAttrPrivate* >(JSObjectGetPrivate(thisObj));
	JSStringRef retString = JSStringCreateWithUTF8CString(privData->arabicaThis->getValue().c_str());
	JSValueRef retObj = JSValueMakeString(ctx, retString);
	JSStringRelease(retString);
	return retObj;

}

JSValueRef JSCAttr::ownerElementAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCAttrPrivate* privData = static_cast<JSCAttr::JSCAttrPrivate* >(JSObjectGetPrivate(thisObj));
	Arabica::DOM::Element<std::string>* arbaicaRet = new Arabica::DOM::Element<std::string>(privData->arabicaThis->getOwnerElement());

	struct JSCElement::JSCElementPrivate* retPrivData = new JSCElement::JSCElementPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->arabicaThis = arbaicaRet;

	JSObjectRef arbaicaRetObj = JSObjectMake(ctx, JSCElement::getTmpl(), retPrivData);
	return arbaicaRetObj;

}

}
}
