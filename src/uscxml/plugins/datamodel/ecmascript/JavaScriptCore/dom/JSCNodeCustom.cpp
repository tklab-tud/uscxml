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