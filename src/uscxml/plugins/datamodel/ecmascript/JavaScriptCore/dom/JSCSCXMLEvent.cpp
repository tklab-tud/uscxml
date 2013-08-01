#include "JSCNode.h"
#include "JSCSCXMLEvent.h"

namespace Arabica {
namespace DOM {

JSClassRef JSCSCXMLEvent::Tmpl;

JSStaticValue JSCSCXMLEvent::staticValues[] = {
	{ "type", typeCustomAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "name", nameAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "origin", originAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "origintype", origintypeAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "raw", rawAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "dom", domAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "sendid", sendidCustomAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "invokeid", invokeidAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },

	{ "INTERNAL", INTERNALConstGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "EXTERNAL", EXTERNALConstGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "PLATFORM", PLATFORMConstGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ 0, 0, 0, 0 }
};

JSStaticFunction JSCSCXMLEvent::staticFunctions[] = {
	{ 0, 0, 0 }
};

JSValueRef JSCSCXMLEvent::nameAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCSCXMLEventPrivate* privData = (struct JSCSCXMLEventPrivate*)JSObjectGetPrivate(object);

	JSStringRef stringRef = JSStringCreateWithUTF8CString(privData->nativeObj->name.c_str());
	JSValueRef retVal = JSValueMakeString(ctx, stringRef);
	JSStringRelease(stringRef);
	return retVal;
}


JSValueRef JSCSCXMLEvent::originAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCSCXMLEventPrivate* privData = (struct JSCSCXMLEventPrivate*)JSObjectGetPrivate(object);

	if (privData->nativeObj->origin.length() == 0)
		return JSValueMakeUndefined(ctx);
	JSStringRef stringRef = JSStringCreateWithUTF8CString(privData->nativeObj->origin.c_str());
	JSValueRef retVal = JSValueMakeString(ctx, stringRef);
	JSStringRelease(stringRef);
	return retVal;
}


JSValueRef JSCSCXMLEvent::origintypeAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCSCXMLEventPrivate* privData = (struct JSCSCXMLEventPrivate*)JSObjectGetPrivate(object);

	if (privData->nativeObj->origintype.length() == 0)
		return JSValueMakeUndefined(ctx);
	JSStringRef stringRef = JSStringCreateWithUTF8CString(privData->nativeObj->origintype.c_str());
	JSValueRef retVal = JSValueMakeString(ctx, stringRef);
	JSStringRelease(stringRef);
	return retVal;
}


JSValueRef JSCSCXMLEvent::rawAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCSCXMLEventPrivate* privData = (struct JSCSCXMLEventPrivate*)JSObjectGetPrivate(object);

	if (privData->nativeObj->raw.length() == 0)
		return JSValueMakeUndefined(ctx);
	JSStringRef stringRef = JSStringCreateWithUTF8CString(privData->nativeObj->raw.c_str());
	JSValueRef retVal = JSValueMakeString(ctx, stringRef);
	JSStringRelease(stringRef);
	return retVal;
}


JSValueRef JSCSCXMLEvent::domAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCSCXMLEventPrivate* privData = (struct JSCSCXMLEventPrivate*)JSObjectGetPrivate(object);

	if (!privData->nativeObj->dom) return JSValueMakeUndefined(ctx);
	Arabica::DOM::Node<std::string>* arabicaRet = new Arabica::DOM::Node<std::string>(privData->nativeObj->dom);

	JSClassRef arbaicaRetClass = JSCNode::getTmpl();

	struct JSCNode::JSCNodePrivate* retPrivData = new JSCNode::JSCNodePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = arabicaRet;

	JSObjectRef arbaicaRetObj = JSObjectMake(ctx, arbaicaRetClass, arabicaRet);
	return arbaicaRetObj;
}


JSValueRef JSCSCXMLEvent::invokeidAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCSCXMLEventPrivate* privData = (struct JSCSCXMLEventPrivate*)JSObjectGetPrivate(object);

	if (privData->nativeObj->invokeid.length() == 0)
		return JSValueMakeUndefined(ctx);
	JSStringRef stringRef = JSStringCreateWithUTF8CString(privData->nativeObj->invokeid.c_str());
	JSValueRef retVal = JSValueMakeString(ctx, stringRef);
	JSStringRelease(stringRef);
	return retVal;
}

JSValueRef JSCSCXMLEvent::INTERNALConstGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef *exception) {
	return JSValueMakeNumber(ctx, 1);
}

JSValueRef JSCSCXMLEvent::EXTERNALConstGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef *exception) {
	return JSValueMakeNumber(ctx, 2);
}

JSValueRef JSCSCXMLEvent::PLATFORMConstGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef *exception) {
	return JSValueMakeNumber(ctx, 3);
}


}
}
