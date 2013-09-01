#include "JSCCharacterData.h"
#include "JSCText.h"

namespace Arabica {
namespace DOM {

JSClassRef JSCText::Tmpl;

JSStaticValue JSCText::staticValues[] = {

	{ 0, 0, 0, 0 }
};

JSStaticFunction JSCText::staticFunctions[] = {
	{ "splitText", splitTextCallback, kJSPropertyAttributeDontDelete },
	{ 0, 0, 0 }
};

JSValueRef JSCText::splitTextCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {

	struct JSCTextPrivate* privData = (struct JSCTextPrivate*)JSObjectGetPrivate(thisObj);

	if (false) {
	} else if (argumentCount == 1 &&
	           JSValueIsNumber(ctx, arguments[0])) {
		unsigned long localOffset = (unsigned long)JSValueToNumber(ctx, arguments[0], exception);

		Arabica::DOM::Text<std::string>* retVal = new Arabica::DOM::Text<std::string>(privData->nativeObj->splitText(localOffset));
		JSClassRef retClass = JSCText::getTmpl();

		struct JSCText::JSCTextPrivate* retPrivData = new JSCText::JSCTextPrivate();
		retPrivData->dom = privData->dom;
		retPrivData->nativeObj = retVal;

		JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

		return retObj;

	}

	JSStringRef exceptionString = JSStringCreateWithUTF8CString("Parameter mismatch while calling splitText");
	*exception = JSValueMakeString(ctx, exceptionString);
	JSStringRelease(exceptionString);
	return JSValueMakeUndefined(ctx);
}

}
}
