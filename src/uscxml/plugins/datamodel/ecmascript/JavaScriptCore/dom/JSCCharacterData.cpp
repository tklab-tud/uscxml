#include "JSCCharacterData.h"
#include "JSCNode.h"

namespace Arabica {
namespace DOM {


JSStaticValue JSCCharacterData::staticValues[] = {
	{ "data", dataAttrGetter, dataAttrSetter, kJSPropertyAttributeDontDelete },
	{ "length", lengthAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },

	{ 0, 0, 0, 0 }
};

JSStaticFunction JSCCharacterData::staticFunctions[] = {
	{ "substringData", substringDataCallback, kJSPropertyAttributeDontDelete },
	{ "appendData", appendDataCallback, kJSPropertyAttributeDontDelete },
	{ "insertData", insertDataCallback, kJSPropertyAttributeDontDelete },
	{ "deleteData", deleteDataCallback, kJSPropertyAttributeDontDelete },
	{ "replaceData", replaceDataCallback, kJSPropertyAttributeDontDelete },
	{ 0, 0, 0 }
};

JSValueRef JSCCharacterData::dataAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCCharacterDataPrivate* privData = static_cast<JSCCharacterData::JSCCharacterDataPrivate* >(JSObjectGetPrivate(thisObj));
	JSStringRef retString = JSStringCreateWithUTF8CString(privData->arabicaThis->getData().c_str());
	JSValueRef retObj = JSValueMakeString(ctx, retString);
	JSStringRelease(retString);
	return retObj;

}

JSValueRef JSCCharacterData::lengthAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCCharacterDataPrivate* privData = static_cast<JSCCharacterData::JSCCharacterDataPrivate* >(JSObjectGetPrivate(thisObj));

	return JSValueMakeNumber(ctx, privData->arabicaThis->getLength());
}

}
}
