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

#include "JSCXPathResult.h"
#include "JSCNode.h"

namespace Arabica {
namespace DOM {

JSValueRef JSCXPathResult::singleNodeValueCustomAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCXPathResultPrivate* privData = (struct JSCXPathResultPrivate*)JSObjectGetPrivate(thisObj);

	Arabica::XPath::NodeSet<std::string> nodeSet = privData->nativeObj->asNodeSet();
	if (nodeSet.size() == 0)
		return JSValueMakeUndefined(ctx);

	Arabica::DOM::Node<std::string>* retVal = new Arabica::DOM::Node<std::string>(nodeSet[0]);
	JSClassRef retClass = JSCNode::getTmpl();

	struct JSCNode::JSCNodePrivate* retPrivData = new JSCNode::JSCNodePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

	return retObj;
}

}
}