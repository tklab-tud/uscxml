#include "V8Float64Array.h"

namespace Arabica {
namespace DOM {

v8::Persistent<v8::FunctionTemplate> V8Float64Array::Tmpl;


v8::Handle<v8::Value> V8Float64Array::lengthAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8Float64ArrayPrivate* privData = V8DOM::toClassPtr<V8Float64ArrayPrivate >(self->GetInternalField(0));

	return v8::Integer::New(privData->nativeObj->getLength());
}
v8::Handle<v8::Value> V8Float64Array::getCallback(const v8::Arguments& args) {
	if (args.Length() < 1)
		throw V8Exception("Wrong number of arguments in get");

	v8::Local<v8::Object> self = args.Holder();
	struct V8Float64ArrayPrivate* privData = V8DOM::toClassPtr<V8Float64ArrayPrivate >(self->GetInternalField(0));
	unsigned long localIndex = args[0]->ToNumber()->Uint32Value();

	double retVal = privData->nativeObj->get(localIndex);

	return v8::Number::New(retVal);
}

v8::Handle<v8::Value> V8Float64Array::setCallback(const v8::Arguments& args) {
	if (args.Length() < 2)
		throw V8Exception("Wrong number of arguments in set");

	v8::Local<v8::Object> self = args.Holder();
	struct V8Float64ArrayPrivate* privData = V8DOM::toClassPtr<V8Float64ArrayPrivate >(self->GetInternalField(0));
	unsigned long localIndex = args[0]->ToNumber()->Uint32Value();
	double localValue = args[1]->ToNumber()->Value();

	privData->nativeObj->set(localIndex, localValue);

	return v8::Undefined();
}

v8::Handle<v8::Value> V8Float64Array::subarrayCallback(const v8::Arguments& args) {
	if (args.Length() < 2)
		throw V8Exception("Wrong number of arguments in subarray");

	v8::Local<v8::Object> self = args.Holder();
	struct V8Float64ArrayPrivate* privData = V8DOM::toClassPtr<V8Float64ArrayPrivate >(self->GetInternalField(0));
	long localStart = args[0]->ToNumber()->Int32Value();
	long localEnd = args[1]->ToNumber()->Int32Value();

	uscxml::Float64Array* retVal = new uscxml::Float64Array(privData->nativeObj->subarray(localStart, localEnd));
	v8::Handle<v8::Function> retCtor = V8Float64Array::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

	struct V8Float64Array::V8Float64ArrayPrivate* retPrivData = new V8Float64Array::V8Float64ArrayPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));

	retObj.MakeWeak(0, V8Float64Array::jsDestructor);
	return retObj;

}

bool V8Float64Array::hasInstance(v8::Handle<v8::Value> value) {
	return getTmpl()->HasInstance(value);
}

}
}
