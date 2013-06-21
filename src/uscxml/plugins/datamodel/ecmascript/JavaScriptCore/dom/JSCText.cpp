#include "JSCCharacterData.h"
#include "JSCText.h"

namespace Arabica {
namespace DOM {


JSStaticValue JSCText::staticValues[] = {

	{ 0, 0, 0, 0 }
};

JSStaticFunction JSCText::staticFunctions[] = {
	{ "splitText", splitTextCallback, kJSPropertyAttributeDontDelete },
	{ 0, 0, 0 }
};
JSValueRef JSCText::splitTextCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) {
	if (argumentCount < 1) {
		std::string errorMsg = "Wrong number of arguments in splitText";
		JSStringRef string = JSStringCreateWithUTF8CString(errorMsg.c_str());
		JSValueRef exceptionString =JSValueMakeString(ctx, string);
		JSStringRelease(string);
		*exception = JSValueToObject(ctx, exceptionString, NULL);
		return NULL;
	}

	struct JSCTextPrivate* privData = (struct JSCTextPrivate*)JSObjectGetPrivate(thisObj);

	unsigned long localOffset = (unsigned long)JSValueToNumber(ctx, arguments[0], exception);

	Arabica::DOM::Text<std::string>* retVal = new Arabica::DOM::Text<std::string>(privData->nativeObj->splitText(localOffset));
	JSClassRef retClass = JSCText::getTmpl();

	struct JSCText::JSCTextPrivate* retPrivData = new JSCText::JSCTextPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

	return retObj;

}


}
}
