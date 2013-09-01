#include "V8ArrayBuffer.h"
#include "V8ArrayBufferView.h"

namespace Arabica {
namespace DOM {

v8::Persistent<v8::FunctionTemplate> V8ArrayBufferView::Tmpl;

v8::Handle<v8::Value> V8ArrayBufferView::bufferAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8ArrayBufferViewPrivate* privData = V8DOM::toClassPtr<V8ArrayBufferViewPrivate >(self->GetInternalField(0));

	if (!privData->nativeObj->getBuffer()) return v8::Undefined();
	uscxml::ArrayBuffer* arbaicaRet = new uscxml::ArrayBuffer(privData->nativeObj->getBuffer());

	v8::Handle<v8::Function> arbaicaRetCtor = V8ArrayBuffer::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> arbaicaRetObj = v8::Persistent<v8::Object>::New(arbaicaRetCtor->NewInstance());

	struct V8ArrayBuffer::V8ArrayBufferPrivate* retPrivData = new V8ArrayBuffer::V8ArrayBufferPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = arbaicaRet;

	arbaicaRetObj->SetInternalField(0, V8DOM::toExternal(retPrivData));
	arbaicaRetObj.MakeWeak(0, V8ArrayBuffer::jsDestructor);
	return arbaicaRetObj;

}

v8::Handle<v8::Value> V8ArrayBufferView::byteOffsetAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8ArrayBufferViewPrivate* privData = V8DOM::toClassPtr<V8ArrayBufferViewPrivate >(self->GetInternalField(0));

	return v8::Integer::New(privData->nativeObj->getByteOffset());
}

v8::Handle<v8::Value> V8ArrayBufferView::byteLengthAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8ArrayBufferViewPrivate* privData = V8DOM::toClassPtr<V8ArrayBufferViewPrivate >(self->GetInternalField(0));

	return v8::Integer::New(privData->nativeObj->getByteLength());
}
bool V8ArrayBufferView::hasInstance(v8::Handle<v8::Value> value) {
	return getTmpl()->HasInstance(value);
}

}
}
