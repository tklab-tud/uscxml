#include "V8SCXMLEvent.h"

namespace Arabica {
namespace DOM {

v8::Handle<v8::Value> V8SCXMLEvent::typeCustomAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	V8SCXMLEvent::V8SCXMLEventPrivate* privData = V8DOM::toClassPtr<V8SCXMLEvent::V8SCXMLEventPrivate >(self->GetInternalField(0));

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
}

}
}