#include "JSCNodeSet.h"
#include "JSCElement.h"
#include "JSCNode.h"

namespace Arabica {
namespace DOM {


bool JSCNodeSet::hasPropertyCustomCallback(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName) {
	size_t propMaxSize = JSStringGetMaximumUTF8CStringSize(propertyName);
	char* propBuffer = new char[propMaxSize];
	JSStringGetUTF8CString(propertyName, propBuffer, propMaxSize);
	std::string propName(propBuffer);
	free(propBuffer);

	std::string base = "0123456789";
	if (propName.find_first_not_of(base) != std::string::npos) {
		return false;
	}

	int index = boost::lexical_cast<int>(propName);
	struct JSCNodeSetPrivate* privData = (struct JSCNodeSetPrivate*)JSObjectGetPrivate(object);

	if (privData->nativeObj->size() < index) {
		return false;
	}

	return true;
}

JSValueRef JSCNodeSet::getPropertyCustomCallback(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef* exception) {
	size_t propMaxSize = JSStringGetMaximumUTF8CStringSize(propertyName);
	char* propBuffer = new char[propMaxSize];
	JSStringGetUTF8CString(propertyName, propBuffer, propMaxSize);
	std::string propName(propBuffer);
	free(propBuffer);

	std::string base = "0123456789";
	if (propName.find_first_not_of(base) != std::string::npos) {
		return JSValueMakeUndefined(ctx);
	}

	int index = boost::lexical_cast<int>(propName);
	struct JSCNodeSetPrivate* privData = (struct JSCNodeSetPrivate*)JSObjectGetPrivate(object);
	if (privData->nativeObj->size() < index) {
		return JSValueMakeUndefined(ctx);
	}

	switch((*privData->nativeObj)[index].getNodeType()) {
	case Node_base::ELEMENT_NODE: {
		Arabica::DOM::Element<std::string>* retVal = new Arabica::DOM::Element<std::string>((*privData->nativeObj)[index]);
		JSClassRef retClass = JSCElement::getTmpl();

		struct JSCElement::JSCElementPrivate* retPrivData = new JSCElement::JSCElementPrivate();
		retPrivData->dom = privData->dom;
		retPrivData->nativeObj = retVal;

		JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

		return retObj;
		break;
	}
	default: {
		Arabica::DOM::Node<std::string>* retVal = new Arabica::DOM::Node<std::string>((*privData->nativeObj)[index]);
		JSClassRef retClass = JSCNode::getTmpl();

		struct JSCNode::JSCNodePrivate* retPrivData = new JSCNode::JSCNodePrivate();
		retPrivData->dom = privData->dom;
		retPrivData->nativeObj = retVal;

		JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

		return retObj;
	}
	}

	return JSValueMakeUndefined(ctx);
}

}
}