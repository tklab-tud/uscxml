#include "JSCNodeSet.h"
#include "JSCXPathResult.h"

namespace Arabica {
namespace DOM {

JSClassRef JSCXPathResult::Tmpl;

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

JSValueRef JSCXPathResult::numberValueAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCXPathResultPrivate* privData = (struct JSCXPathResultPrivate*)JSObjectGetPrivate(object);

	return JSValueMakeNumber(ctx, privData->nativeObj->asNumber());
}


JSValueRef JSCXPathResult::stringValueAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCXPathResultPrivate* privData = (struct JSCXPathResultPrivate*)JSObjectGetPrivate(object);

	JSStringRef stringRef = JSStringCreateWithUTF8CString(privData->nativeObj->asString().c_str());
	JSValueRef retVal = JSValueMakeString(ctx, stringRef);
	JSStringRelease(stringRef);
	return retVal;
}


JSValueRef JSCXPathResult::booleanValueAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCXPathResultPrivate* privData = (struct JSCXPathResultPrivate*)JSObjectGetPrivate(object);

	return JSValueMakeBoolean(ctx, privData->nativeObj->asBool());
}


JSValueRef JSCXPathResult::asNodeSetCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {

	struct JSCXPathResultPrivate* privData = (struct JSCXPathResultPrivate*)JSObjectGetPrivate(thisObj);

	if (false) {
	} else if (argumentCount == 0) {

		Arabica::XPath::NodeSet<std::string>* retVal = new Arabica::XPath::NodeSet<std::string>(privData->nativeObj->asNodeSet());
		JSClassRef retClass = JSCNodeSet::getTmpl();

		struct JSCNodeSet::JSCNodeSetPrivate* retPrivData = new JSCNodeSet::JSCNodeSetPrivate();
		retPrivData->dom = privData->dom;
		retPrivData->nativeObj = retVal;

		JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

		return retObj;

	}

	JSStringRef exceptionString = JSStringCreateWithUTF8CString("Parameter mismatch while calling asNodeSet");
	*exception = JSValueMakeString(ctx, exceptionString);
	JSStringRelease(exceptionString);
	return JSValueMakeUndefined(ctx);
}

JSValueRef JSCXPathResult::asBoolCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {

	struct JSCXPathResultPrivate* privData = (struct JSCXPathResultPrivate*)JSObjectGetPrivate(thisObj);

	if (false) {
	} else if (argumentCount == 0) {

		bool retVal = privData->nativeObj->asBool();

		JSValueRef jscRetVal = JSValueMakeBoolean(ctx, retVal);
		return jscRetVal;
	}

	JSStringRef exceptionString = JSStringCreateWithUTF8CString("Parameter mismatch while calling asBool");
	*exception = JSValueMakeString(ctx, exceptionString);
	JSStringRelease(exceptionString);
	return JSValueMakeUndefined(ctx);
}

JSValueRef JSCXPathResult::asStringCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {

	struct JSCXPathResultPrivate* privData = (struct JSCXPathResultPrivate*)JSObjectGetPrivate(thisObj);

	if (false) {
	} else if (argumentCount == 0) {

		std::string retVal = privData->nativeObj->asString();

		JSStringRef jscString = JSStringCreateWithUTF8CString(retVal.c_str());
		JSValueRef jscRetVal = JSValueMakeString(ctx, jscString);
		JSStringRelease(jscString);
		return jscRetVal;
	}

	JSStringRef exceptionString = JSStringCreateWithUTF8CString("Parameter mismatch while calling asString");
	*exception = JSValueMakeString(ctx, exceptionString);
	JSStringRelease(exceptionString);
	return JSValueMakeUndefined(ctx);
}

JSValueRef JSCXPathResult::asNumberCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {

	struct JSCXPathResultPrivate* privData = (struct JSCXPathResultPrivate*)JSObjectGetPrivate(thisObj);

	if (false) {
	} else if (argumentCount == 0) {

		double retVal = privData->nativeObj->asNumber();

		JSValueRef jscRetVal = JSValueMakeNumber(ctx, retVal);
		return jscRetVal;
	}

	JSStringRef exceptionString = JSStringCreateWithUTF8CString("Parameter mismatch while calling asNumber");
	*exception = JSValueMakeString(ctx, exceptionString);
	JSStringRelease(exceptionString);
	return JSValueMakeUndefined(ctx);
}

}
}
