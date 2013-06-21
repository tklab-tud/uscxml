#include "JSCXPathResult.h"
#include "JSCNode.h"

namespace Arabica {
namespace DOM {

JSValueRef JSCXPathResult::singleNodeValueCustomAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
#if 0
	v8::Local<v8::Object> self = info.Holder();
	V8XPathResultPrivate* privData = V8DOM::toClassPtr<V8XPathResultPrivate >(self->GetInternalField(0));

	Arabica::DOM::Node<std::string>* retVal = new Arabica::DOM::Node<std::string>(privData->nativeObj->asNodeSet()[0]);

	v8::Handle<v8::Function> retCtor = V8Node::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

	struct V8Node::V8NodePrivate* retPrivData = new V8Node::V8NodePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));

	retObj.MakeWeak(0, V8Node::jsDestructor);
	return retObj;
#endif
}

}
}