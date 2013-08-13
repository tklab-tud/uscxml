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