#include "V8Node.h"
#include "V8SCXMLEvent.h"

namespace Arabica {
namespace DOM {

v8::Persistent<v8::FunctionTemplate> V8SCXMLEvent::Tmpl;

v8::Handle<v8::Value> V8SCXMLEvent::nameAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8SCXMLEventPrivate* privData = V8DOM::toClassPtr<V8SCXMLEventPrivate >(self->GetInternalField(0));

	return v8::String::New(privData->nativeObj->name.c_str());
}

v8::Handle<v8::Value> V8SCXMLEvent::originAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8SCXMLEventPrivate* privData = V8DOM::toClassPtr<V8SCXMLEventPrivate >(self->GetInternalField(0));

	if (privData->nativeObj->origin.length() == 0)
		return v8::Undefined();
	return v8::String::New(privData->nativeObj->origin.c_str());
}

v8::Handle<v8::Value> V8SCXMLEvent::origintypeAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8SCXMLEventPrivate* privData = V8DOM::toClassPtr<V8SCXMLEventPrivate >(self->GetInternalField(0));

	if (privData->nativeObj->origintype.length() == 0)
		return v8::Undefined();
	return v8::String::New(privData->nativeObj->origintype.c_str());
}

v8::Handle<v8::Value> V8SCXMLEvent::rawAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8SCXMLEventPrivate* privData = V8DOM::toClassPtr<V8SCXMLEventPrivate >(self->GetInternalField(0));

	if (privData->nativeObj->raw.length() == 0)
		return v8::Undefined();
	return v8::String::New(privData->nativeObj->raw.c_str());
}

v8::Handle<v8::Value> V8SCXMLEvent::domAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8SCXMLEventPrivate* privData = V8DOM::toClassPtr<V8SCXMLEventPrivate >(self->GetInternalField(0));

	if (!privData->nativeObj->dom) return v8::Undefined();
	Arabica::DOM::Node<std::string>* arbaicaRet = new Arabica::DOM::Node<std::string>(privData->nativeObj->dom);

	v8::Handle<v8::Function> arbaicaRetCtor = V8Node::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> arbaicaRetObj = v8::Persistent<v8::Object>::New(arbaicaRetCtor->NewInstance());

	struct V8Node::V8NodePrivate* retPrivData = new V8Node::V8NodePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = arbaicaRet;

	arbaicaRetObj->SetInternalField(0, V8DOM::toExternal(retPrivData));
	arbaicaRetObj.MakeWeak(0, V8Node::jsDestructor);
	return arbaicaRetObj;

}

v8::Handle<v8::Value> V8SCXMLEvent::invokeidAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8SCXMLEventPrivate* privData = V8DOM::toClassPtr<V8SCXMLEventPrivate >(self->GetInternalField(0));

	if (privData->nativeObj->invokeid.length() == 0)
		return v8::Undefined();
	return v8::String::New(privData->nativeObj->invokeid.c_str());
}
bool V8SCXMLEvent::hasInstance(v8::Handle<v8::Value> value) {
	return getTmpl()->HasInstance(value);
}

}
}
