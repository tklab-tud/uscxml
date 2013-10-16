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

#include "JSCSCXMLEvent.h"

namespace Arabica {
namespace DOM {

JSValueRef JSCSCXMLEvent::typeCustomAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCSCXMLEventPrivate* privData = (struct JSCSCXMLEventPrivate*)JSObjectGetPrivate(thisObj);
	JSStringRef stringRef;

	switch (privData->nativeObj->eventType) {
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

	JSValueRef retVal = JSValueMakeString(ctx, stringRef);
	JSStringRelease(stringRef);
	return retVal;
}

JSValueRef JSCSCXMLEvent::sendidCustomAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCSCXMLEventPrivate* privData = (struct JSCSCXMLEventPrivate*)JSObjectGetPrivate(thisObj);
	JSStringRef stringRef;

	if (privData->nativeObj->sendid.length() == 0 || privData->nativeObj->hideSendId) {
		return JSValueMakeUndefined(ctx);
	} else {
		stringRef = JSStringCreateWithUTF8CString(privData->nativeObj->sendid.c_str());
		JSValueRef retVal = JSValueMakeString(ctx, stringRef);
		JSStringRelease(stringRef);
		return retVal;
	}
}

}
}