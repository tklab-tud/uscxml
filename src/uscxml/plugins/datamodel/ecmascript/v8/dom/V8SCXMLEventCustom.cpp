/**
 *  @file
 *  @author     2012-2013 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
 *  @copyright  Simplified BSD
 *
 *  @cond
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the FreeBSD license as published by the FreeBSD
 *  project.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 *
 *  You should have received a copy of the FreeBSD license along with this
 *  program. If not, see <http://www.opensource.org/licenses/bsd-license>.
 *  @endcond
 */

#include "V8SCXMLEvent.h"

namespace Arabica {
namespace DOM {

v8::Handle<v8::Value> V8SCXMLEvent::typeCustomAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	V8SCXMLEventPrivate* privData = V8DOM::toClassPtr<V8SCXMLEventPrivate >(self->GetInternalField(0));

	switch (privData->nativeObj->eventType) {
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

v8::Handle<v8::Value> V8SCXMLEvent::sendidCustomAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	V8SCXMLEventPrivate* privData = V8DOM::toClassPtr<V8SCXMLEventPrivate >(self->GetInternalField(0));

	if (privData->nativeObj->sendid.length() == 0 || privData->nativeObj->hideSendId)
		return v8::Undefined();
	return v8::String::New(privData->nativeObj->sendid.c_str());
}

}
}