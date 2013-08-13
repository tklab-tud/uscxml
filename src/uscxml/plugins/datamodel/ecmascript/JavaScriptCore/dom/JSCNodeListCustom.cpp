#include "JSCNodeList.h"
#include "JSCElement.h"
#include "JSCNode.h"

namespace Arabica {
namespace DOM {

bool JSCNodeList::hasPropertyCustomCallback(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName) {
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
	struct JSCNodeListPrivate* privData = (struct JSCNodeListPrivate*)JSObjectGetPrivate(object);

	if (privData->nativeObj->getLength() < index) {
		return false;
	}

	return true;
}

JSValueRef JSCNodeList::getPropertyCustomCallback(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef* exception) {
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
	struct JSCNodeListPrivate* privData = (struct JSCNodeListPrivate*)JSObjectGetPrivate(object);
	if (privData->nativeObj->getLength() < index) {
		return JSValueMakeUndefined(ctx);
	}

	switch(privData->nativeObj->item(index).getNodeType()) {
	case Node_base::ELEMENT_NODE: {
		Arabica::DOM::Element<std::string>* retVal = new Arabica::DOM::Element<std::string>(privData->nativeObj->item(index));
		JSClassRef retClass = JSCElement::getTmpl();

		struct JSCElement::JSCElementPrivate* retPrivData = new JSCElement::JSCElementPrivate();
		retPrivData->dom = privData->dom;
		retPrivData->nativeObj = retVal;

		JSObjectRef retObj = JSObjectMake(ctx, retClass, retPrivData);

		return retObj;
		break;
	}
	default: {
		Arabica::DOM::Node<std::string>* retVal = new Arabica::DOM::Node<std::string>(privData->nativeObj->item(index));
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

#if 0
v8::Handle<v8::Value> V8NodeList::indexedPropertyCustomGetter(uint32_t index, const v8::AccessorInfo &info) {
	v8::Local<v8::Object> self = info.Holder();
	V8NodeListPrivate* privData = V8DOM::toClassPtr<V8NodeListPrivate >(self->GetInternalField(0));

	if (privData->nativeObj->getLength() >= index) {
		switch(privData->nativeObj->item(index).getNodeType()) {
		case Node_base::ELEMENT_NODE: {
			Arabica::DOM::Element<std::string>* retVal = new Arabica::DOM::Element<std::string>(privData->nativeObj->item(index));

			v8::Handle<v8::Function> retCtor = V8Element::getTmpl()->GetFunction();
			v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

			struct V8Element::V8ElementPrivate* retPrivData = new V8Element::V8ElementPrivate();
			retPrivData->dom = privData->dom;
			retPrivData->nativeObj = retVal;

			retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));

			retObj.MakeWeak(0, V8Element::jsDestructor);
			return retObj;
		}
		default: {
			Arabica::DOM::Node<std::string>* retVal = new Arabica::DOM::Node<std::string>(privData->nativeObj->item(index));

			v8::Handle<v8::Function> retCtor = V8Node::getTmpl()->GetFunction();
			v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

			struct V8Node::V8NodePrivate* retPrivData = new V8Node::V8NodePrivate();
			retPrivData->dom = privData->dom;
			retPrivData->nativeObj = retVal;

			retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));

			retObj.MakeWeak(0, V8Node::jsDestructor);
			return retObj;
		}
		}
	}

	return v8::Undefined();

}
#endif
}
}