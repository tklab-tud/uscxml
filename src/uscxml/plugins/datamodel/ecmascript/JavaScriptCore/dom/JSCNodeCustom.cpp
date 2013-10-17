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

#include "JSCNode.h"
#include "JSCNamedNodeMap.h"

namespace Arabica {
namespace DOM {

JSValueRef JSCNode::attributesCustomAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {

	struct JSCNodePrivate* privData = (struct JSCNodePrivate*)JSObjectGetPrivate(thisObj);

	if (!privData->nativeObj->hasAttributes()) {
		return JSValueMakeUndefined(ctx);
	}

	Arabica::DOM::NamedNodeMap<std::string>* retVal = new Arabica::DOM::NamedNodeMap<std::string>(privData->nativeObj->getAttributes());
	JSClassRef retClass = JSCNamedNodeMap::getTmpl();

	struct JSCNamedNodeMap::JSCNamedNodeMapPrivate* retPrivData = new JSCNamedNodeMap::JSCNamedNodeMapPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

	return retObj;
}


}
}