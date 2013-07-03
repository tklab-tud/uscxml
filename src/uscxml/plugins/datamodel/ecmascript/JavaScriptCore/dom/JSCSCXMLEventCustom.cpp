#include "JSCSCXMLEvent.h"

namespace Arabica {
namespace DOM {

JSValueRef JSCSCXMLEvent::typeCustomAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCSCXMLEventPrivate* privData = (struct JSCSCXMLEventPrivate*)JSObjectGetPrivate(thisObj);
	JSStringRef stringRef;

	switch (privData->nativeObj->type) {
	case uscxml::Event::INTERNAL:
		stringRef = JSStringCreateWithUTF8CString("internal");
		break;
	case uscxml::Event::EXTERNAL:
		stringRef = JSStringCreateWithUTF8CString("external");
		break;
	case uscxml::Event::PLATFORM:
		stringRef = JSStringCreateWithUTF8CString("platform");
		break;
	default:
		stringRef = JSStringCreateWithUTF8CString("undefined");
		break;
	}
	
	return JSValueMakeString(ctx, stringRef);
}

JSValueRef JSCSCXMLEvent::sendidCustomAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCSCXMLEventPrivate* privData = (struct JSCSCXMLEventPrivate*)JSObjectGetPrivate(thisObj);
	JSStringRef stringRef;

	if (privData->nativeObj->sendid.length() == 0 || privData->nativeObj->hideSendId) {
		return JSValueMakeUndefined(ctx);
	} else {
		stringRef = JSStringCreateWithUTF8CString(privData->nativeObj->sendid.c_str());
		return JSValueMakeString(ctx, stringRef);
	}
}

}
}