#include "JSCAttr.h"
#include "JSCElement.h"
#include "JSCNode.h"

namespace Arabica {
namespace DOM {

JSClassRef JSCAttr::Tmpl;

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

JSValueRef JSCAttr::nameAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCAttrPrivate* privData = (struct JSCAttrPrivate*)JSObjectGetPrivate(object);

	JSStringRef stringRef = JSStringCreateWithUTF8CString(privData->nativeObj->getName().c_str());
	JSValueRef retVal = JSValueMakeString(ctx, stringRef);
	JSStringRelease(stringRef);
	return retVal;
}


JSValueRef JSCAttr::specifiedAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCAttrPrivate* privData = (struct JSCAttrPrivate*)JSObjectGetPrivate(object);

	return JSValueMakeBoolean(ctx, privData->nativeObj->getSpecified());
}


JSValueRef JSCAttr::valueAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCAttrPrivate* privData = (struct JSCAttrPrivate*)JSObjectGetPrivate(object);

	JSStringRef stringRef = JSStringCreateWithUTF8CString(privData->nativeObj->getValue().c_str());
	JSValueRef retVal = JSValueMakeString(ctx, stringRef);
	JSStringRelease(stringRef);
	return retVal;
}


bool JSCAttr::valueAttrSetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef value, JSValueRef* exception) {
	struct JSCAttrPrivate* privData = (struct JSCAttrPrivate*)JSObjectGetPrivate(thisObj);

	JSStringRef stringReflocalValue = JSValueToStringCopy(ctx, value, exception);
	size_t localValueMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalValue);
	char* localValueBuffer = new char[localValueMaxSize];
	JSStringGetUTF8CString(stringReflocalValue, localValueBuffer, localValueMaxSize);
	std::string localValue(localValueBuffer);
	JSStringRelease(stringReflocalValue);
	free(localValueBuffer);

	privData->nativeObj->setValue(localValue);
	return true;
}

JSValueRef JSCAttr::ownerElementAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCAttrPrivate* privData = (struct JSCAttrPrivate*)JSObjectGetPrivate(object);

	if (!privData->nativeObj->getOwnerElement()) return JSValueMakeUndefined(ctx);
	Arabica::DOM::Element<std::string>* arabicaRet = new Arabica::DOM::Element<std::string>(privData->nativeObj->getOwnerElement());

	JSClassRef arbaicaRetClass = JSCElement::getTmpl();

	struct JSCElement::JSCElementPrivate* retPrivData = new JSCElement::JSCElementPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = arabicaRet;

	JSObjectRef arbaicaRetObj = JSObjectMake(ctx, arbaicaRetClass, arabicaRet);
	return arbaicaRetObj;
}


}
}
