#include "V8ArrayBuffer.h"
#include "V8ArrayBufferView.h"
#include "V8Uint8ClampedArray.h"

namespace Arabica {
namespace DOM {

v8::Persistent<v8::FunctionTemplate> V8Uint8ClampedArray::Tmpl;
v8::Persistent<v8::FunctionTemplate> V8Uint8ClampedArray::Constr;

v8::Handle<v8::Value> V8Uint8ClampedArray::constructor(const v8::Arguments& args) {
	if (!args.IsConstructCall())
		return v8::ThrowException(v8::String::New("Cannot call constructor as function"));

	uscxml::Uint8ClampedArray* localInstance = NULL;
	if (false) {
	} else if (args.Length() == 3 &&
	           args[0]->IsObject() && V8ArrayBuffer::hasInstance(args[0]) &&
	           args[1]->IsUint32() &&
	           args[2]->IsUint32()) {

		uscxml::ArrayBuffer* localBuffer = V8DOM::toClassPtr<V8ArrayBuffer::V8ArrayBufferPrivate >(args[0]->ToObject()->GetInternalField(0))->nativeObj;
		unsigned long localByteOffset = args[1]->ToNumber()->Uint32Value();
		unsigned long localLength = args[2]->ToNumber()->Uint32Value();
		localInstance = new uscxml::Uint8ClampedArray(localBuffer, localByteOffset, localLength);

	} else if (args.Length() == 2 &&
	           args[0]->IsObject() && V8ArrayBuffer::hasInstance(args[0]) &&
	           args[1]->IsUint32()) {

		uscxml::ArrayBuffer* localBuffer = V8DOM::toClassPtr<V8ArrayBuffer::V8ArrayBufferPrivate >(args[0]->ToObject()->GetInternalField(0))->nativeObj;
		unsigned long localByteOffset = args[1]->ToNumber()->Uint32Value();
		localInstance = new uscxml::Uint8ClampedArray(localBuffer, localByteOffset);

	} else if (args.Length() == 1 &&
	           args[0]->IsObject() && V8Uint8ClampedArray::hasInstance(args[0])) {

		uscxml::Uint8ClampedArray* localArray = V8DOM::toClassPtr<V8Uint8ClampedArray::V8Uint8ClampedArrayPrivate >(args[0]->ToObject()->GetInternalField(0))->nativeObj;
		localInstance = new uscxml::Uint8ClampedArray(localArray);

	} else if (args.Length() == 1 &&
	           args[0]->IsObject() && V8ArrayBuffer::hasInstance(args[0])) {

		uscxml::ArrayBuffer* localBuffer = V8DOM::toClassPtr<V8ArrayBuffer::V8ArrayBufferPrivate >(args[0]->ToObject()->GetInternalField(0))->nativeObj;
		localInstance = new uscxml::Uint8ClampedArray(localBuffer);

	} else if (args.Length() == 1 &&
	           args[0]->IsUint32()) {

		unsigned long localLength = args[0]->ToNumber()->Uint32Value();
		localInstance = new uscxml::Uint8ClampedArray(localLength);

	} else if (args.Length() == 1 &&
	           args[0]->IsArray()) {

		std::vector<unsigned char> localArray;
		v8::Handle<v8::Array> localArrayArray(v8::Array::Cast(*args[0]));
		for (int i = 0; i < localArrayArray->Length(); i++) {
			localArray.push_back(localArrayArray->Get(i)->ToUint32()->Value());
		}
		localInstance = new uscxml::Uint8ClampedArray(localArray);

	}
	if (!localInstance) {
		throw V8Exception("Parameter mismatch while calling constructor for Uint8ClampedArray");
		return v8::Undefined();
	}

	v8::Handle<v8::Function> retCtor = V8Uint8ClampedArray::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

	struct V8Uint8ClampedArray::V8Uint8ClampedArrayPrivate* retPrivData = new V8Uint8ClampedArray::V8Uint8ClampedArrayPrivate();
	retPrivData->nativeObj = localInstance;

	retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));

	retObj.MakeWeak(0, V8Uint8ClampedArray::jsDestructor);
	return retObj;
}

v8::Handle<v8::Value> V8Uint8ClampedArray::lengthAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8Uint8ClampedArrayPrivate* privData = V8DOM::toClassPtr<V8Uint8ClampedArrayPrivate >(self->GetInternalField(0));

	return v8::Integer::New(privData->nativeObj->getLength());
}

v8::Handle<v8::Value> V8Uint8ClampedArray::getCallback(const v8::Arguments& args) {

	v8::Local<v8::Object> self = args.Holder();
	struct V8Uint8ClampedArrayPrivate* privData = V8DOM::toClassPtr<V8Uint8ClampedArrayPrivate >(self->GetInternalField(0));
	if (false) {
	} else if (args.Length() == 1 &&
	           args[0]->IsUint32()) {
		unsigned long localIndex = args[0]->ToNumber()->Uint32Value();

		unsigned char retVal = privData->nativeObj->get(localIndex);

		return v8::Number::New(retVal);
	}
	throw V8Exception("Parameter mismatch while calling get");
	return v8::Undefined();
}

v8::Handle<v8::Value> V8Uint8ClampedArray::setCallback(const v8::Arguments& args) {

	v8::Local<v8::Object> self = args.Holder();
	struct V8Uint8ClampedArrayPrivate* privData = V8DOM::toClassPtr<V8Uint8ClampedArrayPrivate >(self->GetInternalField(0));
	if (false) {
	} else if (args.Length() == 2 &&
	           args[0]->IsObject() && V8Uint8ClampedArray::hasInstance(args[0]) &&
	           args[1]->IsUint32()) {
		uscxml::Uint8ClampedArray* localArray = V8DOM::toClassPtr<V8Uint8ClampedArray::V8Uint8ClampedArrayPrivate >(args[0]->ToObject()->GetInternalField(0))->nativeObj;
		unsigned long localOffset = args[1]->ToNumber()->Uint32Value();

		privData->nativeObj->set(localArray, localOffset);

		return v8::Undefined();
	} else if (args.Length() == 2 &&
	           args[0]->IsUint32() &&
	           args[1]->IsUint32()) {
		unsigned long localIndex = args[0]->ToNumber()->Uint32Value();
		unsigned char localValue = args[1]->ToNumber()->Uint32Value();

		privData->nativeObj->set(localIndex, localValue);

		return v8::Undefined();
	} else if (args.Length() == 2 &&
	           args[0]->IsArray() &&
	           args[1]->IsUint32()) {
		std::vector<unsigned char> localArray;
		v8::Handle<v8::Array> localArrayArray(v8::Array::Cast(*args[0]));
		for (int i = 0; i < localArrayArray->Length(); i++) {
			localArray.push_back(localArrayArray->Get(i)->ToUint32()->Value());
		}
		unsigned long localOffset = args[1]->ToNumber()->Uint32Value();

		privData->nativeObj->set(localArray, localOffset);

		return v8::Undefined();
	} else if (args.Length() == 1 &&
	           args[0]->IsObject() && V8Uint8ClampedArray::hasInstance(args[0])) {
		uscxml::Uint8ClampedArray* localArray = V8DOM::toClassPtr<V8Uint8ClampedArray::V8Uint8ClampedArrayPrivate >(args[0]->ToObject()->GetInternalField(0))->nativeObj;

		privData->nativeObj->set(localArray);

		return v8::Undefined();
	} else if (args.Length() == 1 &&
	           args[0]->IsArray()) {
		std::vector<unsigned char> localArray;
		v8::Handle<v8::Array> localArrayArray(v8::Array::Cast(*args[0]));
		for (int i = 0; i < localArrayArray->Length(); i++) {
			localArray.push_back(localArrayArray->Get(i)->ToUint32()->Value());
		}

		privData->nativeObj->set(localArray);

		return v8::Undefined();
	}
	throw V8Exception("Parameter mismatch while calling set");
	return v8::Undefined();
}

v8::Handle<v8::Value> V8Uint8ClampedArray::subarrayCallback(const v8::Arguments& args) {

	v8::Local<v8::Object> self = args.Holder();
	struct V8Uint8ClampedArrayPrivate* privData = V8DOM::toClassPtr<V8Uint8ClampedArrayPrivate >(self->GetInternalField(0));
	if (false) {
	} else if (args.Length() == 2 &&
	           args[0]->IsInt32() &&
	           args[1]->IsInt32()) {
		long localStart = args[0]->ToNumber()->Int32Value();
		long localEnd = args[1]->ToNumber()->Int32Value();

		uscxml::Uint8ClampedArray* retVal = new uscxml::Uint8ClampedArray(privData->nativeObj->subarray(localStart, localEnd));
		v8::Handle<v8::Function> retCtor = V8Uint8ClampedArray::getTmpl()->GetFunction();
		v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

		struct V8Uint8ClampedArray::V8Uint8ClampedArrayPrivate* retPrivData = new V8Uint8ClampedArray::V8Uint8ClampedArrayPrivate();
		retPrivData->dom = privData->dom;
		retPrivData->nativeObj = retVal;

		retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));

		retObj.MakeWeak(0, V8Uint8ClampedArray::jsDestructor);
		return retObj;

	}
	throw V8Exception("Parameter mismatch while calling subarray");
	return v8::Undefined();
}
bool V8Uint8ClampedArray::hasInstance(v8::Handle<v8::Value> value) {
	return getTmpl()->HasInstance(value);
}

}
}
