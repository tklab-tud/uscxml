#include "V8Uint8Array.h"

namespace Arabica {
namespace DOM {

v8::Persistent<v8::FunctionTemplate> V8Uint8Array::Tmpl;


v8::Handle<v8::Value> V8Uint8Array::lengthAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8Uint8ArrayPrivate* privData = V8DOM::toClassPtr<V8Uint8ArrayPrivate >(self->GetInternalField(0));

	return v8::Integer::New(privData->nativeObj->getLength());
}
v8::Handle<v8::Value> V8Uint8Array::getCallback(const v8::Arguments& args) {
	if (args.Length() < 1)
		throw V8Exception("Wrong number of arguments in get");

	v8::Local<v8::Object> self = args.Holder();
	struct V8Uint8ArrayPrivate* privData = V8DOM::toClassPtr<V8Uint8ArrayPrivate >(self->GetInternalField(0));
	unsigned long localIndex = args[0]->ToNumber()->Uint32Value();

	char retVal = privData->nativeObj->get(localIndex);

	return v8::Number::New(retVal);
}

v8::Handle<v8::Value> V8Uint8Array::setCallback(const v8::Arguments& args) {
	if (args.Length() < 2)
		throw V8Exception("Wrong number of arguments in set");

	v8::Local<v8::Object> self = args.Holder();
	struct V8Uint8ArrayPrivate* privData = V8DOM::toClassPtr<V8Uint8ArrayPrivate >(self->GetInternalField(0));
	unsigned long localIndex = args[0]->ToNumber()->Uint32Value();
	unsigned char localValue = args[1]->ToNumber()->Uint32Value();

	privData->nativeObj->set(localIndex, localValue);

	return v8::Undefined();
}

v8::Handle<v8::Value> V8Uint8Array::subarrayCallback(const v8::Arguments& args) {
	if (args.Length() < 2)
		throw V8Exception("Wrong number of arguments in subarray");

	v8::Local<v8::Object> self = args.Holder();
	struct V8Uint8ArrayPrivate* privData = V8DOM::toClassPtr<V8Uint8ArrayPrivate >(self->GetInternalField(0));
	long localStart = args[0]->ToNumber()->Int32Value();
	long localEnd = args[1]->ToNumber()->Int32Value();

	uscxml::Uint8Array* retVal = new uscxml::Uint8Array(privData->nativeObj->subarray(localStart, localEnd));
	v8::Handle<v8::Function> retCtor = V8Uint8Array::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

	struct V8Uint8Array::V8Uint8ArrayPrivate* retPrivData = new V8Uint8Array::V8Uint8ArrayPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));

	retObj.MakeWeak(0, V8Uint8Array::jsDestructor);
	return retObj;

}

bool V8Uint8Array::hasInstance(v8::Handle<v8::Value> value) {
	return getTmpl()->HasInstance(value);
}

}
}
