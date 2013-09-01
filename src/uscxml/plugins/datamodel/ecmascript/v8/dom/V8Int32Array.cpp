#include "V8ArrayBuffer.h"
#include "V8ArrayBufferView.h"
#include "V8Int32Array.h"

namespace Arabica {
namespace DOM {

v8::Persistent<v8::FunctionTemplate> V8Int32Array::Tmpl;
v8::Persistent<v8::FunctionTemplate> V8Int32Array::Constr;

v8::Handle<v8::Value> V8Int32Array::constructor(const v8::Arguments& args) {
	if (!args.IsConstructCall())
		return v8::ThrowException(v8::String::New("Cannot call constructor as function"));

	uscxml::Int32Array* localInstance = NULL;
	if (false) {
	} else if (args.Length() == 3 &&
	           args[0]->IsObject() && V8ArrayBuffer::hasInstance(args[0]) &&
	           args[1]->IsUint32() &&
	           args[2]->IsUint32()) {

		uscxml::ArrayBuffer* localBuffer = V8DOM::toClassPtr<V8ArrayBuffer::V8ArrayBufferPrivate >(args[0]->ToObject()->GetInternalField(0))->nativeObj;
		unsigned long localByteOffset = args[1]->ToNumber()->Uint32Value();
		unsigned long localLength = args[2]->ToNumber()->Uint32Value();
		localInstance = new uscxml::Int32Array(localBuffer, localByteOffset, localLength);

	} else if (args.Length() == 2 &&
	           args[0]->IsObject() && V8ArrayBuffer::hasInstance(args[0]) &&
	           args[1]->IsUint32()) {

		uscxml::ArrayBuffer* localBuffer = V8DOM::toClassPtr<V8ArrayBuffer::V8ArrayBufferPrivate >(args[0]->ToObject()->GetInternalField(0))->nativeObj;
		unsigned long localByteOffset = args[1]->ToNumber()->Uint32Value();
		localInstance = new uscxml::Int32Array(localBuffer, localByteOffset);

	} else if (args.Length() == 1 &&
	           args[0]->IsObject() && V8Int32Array::hasInstance(args[0])) {

		uscxml::Int32Array* localArray = V8DOM::toClassPtr<V8Int32Array::V8Int32ArrayPrivate >(args[0]->ToObject()->GetInternalField(0))->nativeObj;
		localInstance = new uscxml::Int32Array(localArray);

	} else if (args.Length() == 1 &&
	           args[0]->IsObject() && V8ArrayBuffer::hasInstance(args[0])) {

		uscxml::ArrayBuffer* localBuffer = V8DOM::toClassPtr<V8ArrayBuffer::V8ArrayBufferPrivate >(args[0]->ToObject()->GetInternalField(0))->nativeObj;
		localInstance = new uscxml::Int32Array(localBuffer);

	} else if (args.Length() == 1 &&
	           args[0]->IsUint32()) {

		unsigned long localLength = args[0]->ToNumber()->Uint32Value();
		localInstance = new uscxml::Int32Array(localLength);

	} else if (args.Length() == 1 &&
	           args[0]->IsArray()) {

		std::vector<long> localArray;
		v8::Handle<v8::Array> localArrayArray(v8::Array::Cast(*args[0]));
		for (int i = 0; i < localArrayArray->Length(); i++) {
			localArray.push_back(localArrayArray->Get(i)->ToInteger()->Value());
		}
		localInstance = new uscxml::Int32Array(localArray);

	}
	if (!localInstance) {
		throw V8Exception("Parameter mismatch while calling constructor for Int32Array");
		return v8::Undefined();
	}

	v8::Handle<v8::Function> retCtor = V8Int32Array::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

	struct V8Int32Array::V8Int32ArrayPrivate* retPrivData = new V8Int32Array::V8Int32ArrayPrivate();
	retPrivData->nativeObj = localInstance;

	retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));

	retObj.MakeWeak(0, V8Int32Array::jsDestructor);
	return retObj;
}

v8::Handle<v8::Value> V8Int32Array::lengthAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8Int32ArrayPrivate* privData = V8DOM::toClassPtr<V8Int32ArrayPrivate >(self->GetInternalField(0));

	return v8::Integer::New(privData->nativeObj->getLength());
}

v8::Handle<v8::Value> V8Int32Array::getCallback(const v8::Arguments& args) {

	v8::Local<v8::Object> self = args.Holder();
	struct V8Int32ArrayPrivate* privData = V8DOM::toClassPtr<V8Int32ArrayPrivate >(self->GetInternalField(0));
	if (false) {
	} else if (args.Length() == 1 &&
	           args[0]->IsUint32()) {
		unsigned long localIndex = args[0]->ToNumber()->Uint32Value();

		long retVal = privData->nativeObj->get(localIndex);

		return v8::Number::New(retVal);
	}
	throw V8Exception("Parameter mismatch while calling get");
	return v8::Undefined();
}

v8::Handle<v8::Value> V8Int32Array::setCallback(const v8::Arguments& args) {

	v8::Local<v8::Object> self = args.Holder();
	struct V8Int32ArrayPrivate* privData = V8DOM::toClassPtr<V8Int32ArrayPrivate >(self->GetInternalField(0));
	if (false) {
	} else if (args.Length() == 2 &&
	           args[0]->IsObject() && V8Int32Array::hasInstance(args[0]) &&
	           args[1]->IsUint32()) {
		uscxml::Int32Array* localArray = V8DOM::toClassPtr<V8Int32Array::V8Int32ArrayPrivate >(args[0]->ToObject()->GetInternalField(0))->nativeObj;
		unsigned long localOffset = args[1]->ToNumber()->Uint32Value();

		privData->nativeObj->set(localArray, localOffset);

		return v8::Undefined();
	} else if (args.Length() == 2 &&
	           args[0]->IsUint32() &&
	           args[1]->IsInt32()) {
		unsigned long localIndex = args[0]->ToNumber()->Uint32Value();
		long localValue = args[1]->ToNumber()->Int32Value();

		privData->nativeObj->set(localIndex, localValue);

		return v8::Undefined();
	} else if (args.Length() == 2 &&
	           args[0]->IsArray() &&
	           args[1]->IsUint32()) {
		std::vector<long> localArray;
		v8::Handle<v8::Array> localArrayArray(v8::Array::Cast(*args[0]));
		for (int i = 0; i < localArrayArray->Length(); i++) {
			localArray.push_back(localArrayArray->Get(i)->ToInteger()->Value());
		}
		unsigned long localOffset = args[1]->ToNumber()->Uint32Value();

		privData->nativeObj->set(localArray, localOffset);

		return v8::Undefined();
	} else if (args.Length() == 1 &&
	           args[0]->IsObject() && V8Int32Array::hasInstance(args[0])) {
		uscxml::Int32Array* localArray = V8DOM::toClassPtr<V8Int32Array::V8Int32ArrayPrivate >(args[0]->ToObject()->GetInternalField(0))->nativeObj;

		privData->nativeObj->set(localArray);

		return v8::Undefined();
	} else if (args.Length() == 1 &&
	           args[0]->IsArray()) {
		std::vector<long> localArray;
		v8::Handle<v8::Array> localArrayArray(v8::Array::Cast(*args[0]));
		for (int i = 0; i < localArrayArray->Length(); i++) {
			localArray.push_back(localArrayArray->Get(i)->ToInteger()->Value());
		}

		privData->nativeObj->set(localArray);

		return v8::Undefined();
	}
	throw V8Exception("Parameter mismatch while calling set");
	return v8::Undefined();
}

v8::Handle<v8::Value> V8Int32Array::subarrayCallback(const v8::Arguments& args) {

	v8::Local<v8::Object> self = args.Holder();
	struct V8Int32ArrayPrivate* privData = V8DOM::toClassPtr<V8Int32ArrayPrivate >(self->GetInternalField(0));
	if (false) {
	} else if (args.Length() == 2 &&
	           args[0]->IsInt32() &&
	           args[1]->IsInt32()) {
		long localStart = args[0]->ToNumber()->Int32Value();
		long localEnd = args[1]->ToNumber()->Int32Value();

		uscxml::Int32Array* retVal = new uscxml::Int32Array(privData->nativeObj->subarray(localStart, localEnd));
		v8::Handle<v8::Function> retCtor = V8Int32Array::getTmpl()->GetFunction();
		v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

		struct V8Int32Array::V8Int32ArrayPrivate* retPrivData = new V8Int32Array::V8Int32ArrayPrivate();
		retPrivData->dom = privData->dom;
		retPrivData->nativeObj = retVal;

		retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));

		retObj.MakeWeak(0, V8Int32Array::jsDestructor);
		return retObj;

	}
	throw V8Exception("Parameter mismatch while calling subarray");
	return v8::Undefined();
}
bool V8Int32Array::hasInstance(v8::Handle<v8::Value> value) {
	return getTmpl()->HasInstance(value);
}

}
}
