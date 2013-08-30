#include "V8ArrayBuffer.h"

namespace Arabica {
namespace DOM {

v8::Persistent<v8::FunctionTemplate> V8ArrayBuffer::Tmpl;


v8::Handle<v8::Value> V8ArrayBuffer::byteLengthAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8ArrayBufferPrivate* privData = V8DOM::toClassPtr<V8ArrayBufferPrivate >(self->GetInternalField(0));

	return v8::Integer::New(privData->nativeObj->getByteLength());
}
v8::Handle<v8::Value> V8ArrayBuffer::sliceCallback(const v8::Arguments& args) {
	if (args.Length() < 2)
		throw V8Exception("Wrong number of arguments in slice");

	v8::Local<v8::Object> self = args.Holder();
	struct V8ArrayBufferPrivate* privData = V8DOM::toClassPtr<V8ArrayBufferPrivate >(self->GetInternalField(0));
	long localBegin = args[0]->ToNumber()->Int32Value();
	long localEnd = args[1]->ToNumber()->Int32Value();

	uscxml::ArrayBuffer* retVal = new uscxml::ArrayBuffer(privData->nativeObj->slice(localBegin, localEnd));
	v8::Handle<v8::Function> retCtor = V8ArrayBuffer::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

	struct V8ArrayBuffer::V8ArrayBufferPrivate* retPrivData = new V8ArrayBuffer::V8ArrayBufferPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));

	retObj.MakeWeak(0, V8ArrayBuffer::jsDestructor);
	return retObj;

}

v8::Handle<v8::Value> V8ArrayBuffer::isViewCallback(const v8::Arguments& args) {
	if (args.Length() < 1)
		throw V8Exception("Wrong number of arguments in isView");

	v8::Local<v8::Object> self = args.Holder();
	struct V8ArrayBufferPrivate* privData = V8DOM::toClassPtr<V8ArrayBufferPrivate >(self->GetInternalField(0));
	void* localValue = v8::External::Unwrap(args[0]->ToObject()->GetInternalField(0));

	bool retVal = privData->nativeObj->isView(localValue);

	return v8::Boolean::New(retVal);
}

bool V8ArrayBuffer::hasInstance(v8::Handle<v8::Value> value) {
	return getTmpl()->HasInstance(value);
}

}
}
