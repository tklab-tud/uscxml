#include "V8Attr.h"
#include "V8Element.h"
#include "V8Node.h"

namespace Arabica {
namespace DOM {

v8::Persistent<v8::FunctionTemplate> V8Attr::Tmpl;

v8::Handle<v8::Value> V8Attr::nameAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8AttrPrivate* privData = V8DOM::toClassPtr<V8AttrPrivate >(self->GetInternalField(0));

	return v8::String::New(privData->nativeObj->getName().c_str());
}

v8::Handle<v8::Value> V8Attr::specifiedAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8AttrPrivate* privData = V8DOM::toClassPtr<V8AttrPrivate >(self->GetInternalField(0));

	return v8::Boolean::New(privData->nativeObj->getSpecified());
}

v8::Handle<v8::Value> V8Attr::valueAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8AttrPrivate* privData = V8DOM::toClassPtr<V8AttrPrivate >(self->GetInternalField(0));

	return v8::String::New(privData->nativeObj->getValue().c_str());
}

void V8Attr::valueAttrSetter(v8::Local<v8::String> property, v8::Local<v8::Value> value, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8AttrPrivate* privData = V8DOM::toClassPtr<V8AttrPrivate >(self->GetInternalField(0));
	v8::String::AsciiValue localValue(value);
	privData->nativeObj->setValue(*localValue);
}

v8::Handle<v8::Value> V8Attr::ownerElementAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8AttrPrivate* privData = V8DOM::toClassPtr<V8AttrPrivate >(self->GetInternalField(0));

	if (!privData->nativeObj->getOwnerElement()) return v8::Undefined();
	Arabica::DOM::Element<std::string>* arbaicaRet = new Arabica::DOM::Element<std::string>(privData->nativeObj->getOwnerElement());

	v8::Handle<v8::Function> arbaicaRetCtor = V8Element::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> arbaicaRetObj = v8::Persistent<v8::Object>::New(arbaicaRetCtor->NewInstance());

	struct V8Element::V8ElementPrivate* retPrivData = new V8Element::V8ElementPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = arbaicaRet;

	arbaicaRetObj->SetInternalField(0, V8DOM::toExternal(retPrivData));
	arbaicaRetObj.MakeWeak(0, V8Element::jsDestructor);
	return arbaicaRetObj;

}
bool V8Attr::hasInstance(v8::Handle<v8::Value> value) {
	return getTmpl()->HasInstance(value);
}

}
}
