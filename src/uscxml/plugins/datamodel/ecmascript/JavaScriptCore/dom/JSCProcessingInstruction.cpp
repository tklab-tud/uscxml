#include "JSCNode.h"
#include "JSCProcessingInstruction.h"

namespace Arabica {
namespace DOM {

JSClassRef JSCProcessingInstruction::Tmpl;

JSStaticValue JSCProcessingInstruction::staticValues[] = {
	{ "target", targetAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "data", dataAttrGetter, dataAttrSetter, kJSPropertyAttributeDontDelete },

	{ 0, 0, 0, 0 }
};

JSStaticFunction JSCProcessingInstruction::staticFunctions[] = {
	{ 0, 0, 0 }
};

JSValueRef JSCProcessingInstruction::targetAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCProcessingInstructionPrivate* privData = (struct JSCProcessingInstructionPrivate*)JSObjectGetPrivate(object);

	JSStringRef stringRef = JSStringCreateWithUTF8CString(privData->nativeObj->getTarget().c_str());
	JSValueRef retVal = JSValueMakeString(ctx, stringRef);
	JSStringRelease(stringRef);
	return retVal;
}


JSValueRef JSCProcessingInstruction::dataAttrGetter(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception) {
	struct JSCProcessingInstructionPrivate* privData = (struct JSCProcessingInstructionPrivate*)JSObjectGetPrivate(object);

	JSStringRef stringRef = JSStringCreateWithUTF8CString(privData->nativeObj->getData().c_str());
	JSValueRef retVal = JSValueMakeString(ctx, stringRef);
	JSStringRelease(stringRef);
	return retVal;
}


bool JSCProcessingInstruction::dataAttrSetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef value, JSValueRef* exception) {
	struct JSCProcessingInstructionPrivate* privData = (struct JSCProcessingInstructionPrivate*)JSObjectGetPrivate(thisObj);

	JSStringRef stringReflocalData = JSValueToStringCopy(ctx, value, exception);
	size_t localDataMaxSize = JSStringGetMaximumUTF8CStringSize(stringReflocalData);
	char* localDataBuffer = new char[localDataMaxSize];
	JSStringGetUTF8CString(stringReflocalData, localDataBuffer, sizeof(localDataBuffer));
	std::string localData(localDataBuffer, localDataMaxSize);
	free(localDataBuffer);

	privData->nativeObj->setData(localData);
	return true;
}

}
}
