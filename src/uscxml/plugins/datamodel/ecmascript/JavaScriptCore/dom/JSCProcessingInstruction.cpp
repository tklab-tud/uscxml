#include "JSCNode.h"
#include "JSCProcessingInstruction.h"

namespace Arabica {
namespace DOM {


JSStaticValue JSCProcessingInstruction::staticValues[] = {
	{ "target", targetAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "data", dataAttrGetter, dataAttrSetter, kJSPropertyAttributeDontDelete },

	{ 0, 0, 0, 0 }
};

JSStaticFunction JSCProcessingInstruction::staticFunctions[] = {
	{ 0, 0, 0 }
};

JSValueRef JSCProcessingInstruction::targetAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCProcessingInstructionPrivate* privData = static_cast<JSCProcessingInstruction::JSCProcessingInstructionPrivate* >(JSObjectGetPrivate(thisObj));
	JSStringRef retString = JSStringCreateWithUTF8CString(privData->arabicaThis->getTarget().c_str());
	JSValueRef retObj = JSValueMakeString(ctx, retString);
	JSStringRelease(retString);
	return retObj;

}

JSValueRef JSCProcessingInstruction::dataAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCProcessingInstructionPrivate* privData = static_cast<JSCProcessingInstruction::JSCProcessingInstructionPrivate* >(JSObjectGetPrivate(thisObj));
	JSStringRef retString = JSStringCreateWithUTF8CString(privData->arabicaThis->getData().c_str());
	JSValueRef retObj = JSValueMakeString(ctx, retString);
	JSStringRelease(retString);
	return retObj;

}

}
}
