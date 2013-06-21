#include "JSCSCXMLEvent.h"

namespace Arabica {
namespace DOM {

JSValueRef JSCSCXMLEvent::typeCustomAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
#if 0
	v8::Local<v8::Object> self = info.Holder();
	V8SCXMLEventPrivate* privData = V8DOM::toClassPtr<V8SCXMLEventPrivate >(self->GetInternalField(0));

	switch (privData->nativeObj->type) {
	case uscxml::Event::INTERNAL:
		return v8::String::New("internal");
		break;
	case uscxml::Event::EXTERNAL:
		return v8::String::New("external");
		break;
	case uscxml::Event::PLATFORM:
		return v8::String::New("platform");
		break;
	default:
		break;
	}
	return v8::String::New("unknown");
#endif
}

JSValueRef JSCSCXMLEvent::sendidCustomAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
#if 0
	v8::Local<v8::Object> self = info.Holder();
	V8SCXMLEventPrivate* privData = V8DOM::toClassPtr<V8SCXMLEventPrivate >(self->GetInternalField(0));

	if (privData->nativeObj->sendid.length() == 0 || privData->nativeObj->hideSendId)
		return v8::Undefined();
	return v8::String::New(privData->nativeObj->sendid.c_str());
#endif
}

}
}