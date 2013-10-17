/**
 *  @file
 *  @author     2012-2013 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
 *  @copyright  Simplified BSD
 *
 *  @cond
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the FreeBSD license as published by the FreeBSD
 *  project.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 *
 *  You should have received a copy of the FreeBSD license along with this
 *  program. If not, see <http://www.opensource.org/licenses/bsd-license>.
 *  @endcond
 */

#include "../../TypedArray.h"
#include "V8ArrayBuffer.h"
#include "V8Int8Array.h"
#include "V8Uint8Array.h"
#include "V8Uint8ClampedArray.h"
#include "V8Int16Array.h"
#include "V8Uint16Array.h"
#include "V8Int32Array.h"
#include "V8Uint32Array.h"
#include "V8Float32Array.h"
#include "V8Float64Array.h"
#include "V8DataView.h"

#define V8_TYPED_ARRAY_GET_PRIVATE(type) \
v8::Local<v8::Object> self = info.Holder(); \
uscxml::type* array = V8DOM::toClassPtr<V8##type##Private >(self->GetInternalField(0))->nativeObj; \
if (index > array->getLength()) \
	return v8::Undefined();


namespace Arabica {
namespace DOM {

v8::Handle<v8::Value> V8Int8Array::indexedPropertyCustomSetter(unsigned int index, v8::Local<v8::Value> value, const v8::AccessorInfo &info) {
	V8_TYPED_ARRAY_GET_PRIVATE(Int8Array);
	array->set(index, value->ToInt32()->Value());
	return value;
}

v8::Handle<v8::Value> V8Int16Array::indexedPropertyCustomSetter(unsigned int index, v8::Local<v8::Value> value, const v8::AccessorInfo &info) {
	V8_TYPED_ARRAY_GET_PRIVATE(Int16Array);
	array->set(index, value->ToInt32()->Value());
	return value;
}

v8::Handle<v8::Value> V8Int32Array::indexedPropertyCustomSetter(unsigned int index, v8::Local<v8::Value> value, const v8::AccessorInfo &info) {
	V8_TYPED_ARRAY_GET_PRIVATE(Int32Array);
	array->set(index, value->ToInt32()->Value());
	return value;
}

v8::Handle<v8::Value> V8Uint8Array::indexedPropertyCustomSetter(unsigned int index, v8::Local<v8::Value> value, const v8::AccessorInfo &info) {
	V8_TYPED_ARRAY_GET_PRIVATE(Uint8Array);
	array->set(index, value->ToUint32()->Value());
	return value;
}

v8::Handle<v8::Value> V8Uint16Array::indexedPropertyCustomSetter(unsigned int index, v8::Local<v8::Value> value, const v8::AccessorInfo &info) {
	V8_TYPED_ARRAY_GET_PRIVATE(Uint16Array);
	array->set(index, value->ToUint32()->Value());
	return value;
}

v8::Handle<v8::Value> V8Uint32Array::indexedPropertyCustomSetter(unsigned int index, v8::Local<v8::Value> value, const v8::AccessorInfo &info) {
	V8_TYPED_ARRAY_GET_PRIVATE(Uint32Array);
	array->set(index, value->ToUint32()->Value());
	return value;
}

v8::Handle<v8::Value> V8Float32Array::indexedPropertyCustomSetter(unsigned int index, v8::Local<v8::Value> value, const v8::AccessorInfo &info) {
	V8_TYPED_ARRAY_GET_PRIVATE(Float32Array);
	array->set(index, value->ToNumber()->Value());
	return value;
}

v8::Handle<v8::Value> V8Float64Array::indexedPropertyCustomSetter(unsigned int index, v8::Local<v8::Value> value, const v8::AccessorInfo &info) {
	V8_TYPED_ARRAY_GET_PRIVATE(Float64Array);
	array->set(index, value->ToNumber()->Value());
	return value;
}

v8::Handle<v8::Value> V8Uint8ClampedArray::indexedPropertyCustomSetter(unsigned int index, v8::Local<v8::Value> value, const v8::AccessorInfo &info) {
	V8_TYPED_ARRAY_GET_PRIVATE(Uint8ClampedArray);
	array->set(index, value->ToUint32()->Value() & 0xff);
	return value;
}

// ----------------

v8::Handle<v8::Value> V8Int8Array::indexedPropertyCustomGetter(unsigned int index, const v8::AccessorInfo &info) {
	V8_TYPED_ARRAY_GET_PRIVATE(Int8Array);
	return v8::Int32::New(array->get(index));
}

v8::Handle<v8::Value> V8Int16Array::indexedPropertyCustomGetter(unsigned int index, const v8::AccessorInfo &info) {
	V8_TYPED_ARRAY_GET_PRIVATE(Int16Array);
	return v8::Int32::New(array->get(index));
}

v8::Handle<v8::Value> V8Int32Array::indexedPropertyCustomGetter(unsigned int index, const v8::AccessorInfo &info) {
	V8_TYPED_ARRAY_GET_PRIVATE(Int32Array);
	return v8::Int32::New(array->get(index));
}

v8::Handle<v8::Value> V8Uint8Array::indexedPropertyCustomGetter(unsigned int index, const v8::AccessorInfo &info) {
	V8_TYPED_ARRAY_GET_PRIVATE(Uint8Array);
	return v8::Uint32::New(array->get(index));
}

v8::Handle<v8::Value> V8Uint16Array::indexedPropertyCustomGetter(unsigned int index, const v8::AccessorInfo &info) {
	V8_TYPED_ARRAY_GET_PRIVATE(Uint16Array);
	return v8::Uint32::New(array->get(index));
}

v8::Handle<v8::Value> V8Uint32Array::indexedPropertyCustomGetter(unsigned int index, const v8::AccessorInfo &info) {
	V8_TYPED_ARRAY_GET_PRIVATE(Uint32Array);
	return v8::Uint32::New(array->get(index));
}

v8::Handle<v8::Value> V8Float32Array::indexedPropertyCustomGetter(unsigned int index, const v8::AccessorInfo &info) {
	V8_TYPED_ARRAY_GET_PRIVATE(Float32Array);
	return v8::Number::New(array->get(index));
}

v8::Handle<v8::Value> V8Float64Array::indexedPropertyCustomGetter(unsigned int index, const v8::AccessorInfo &info) {
	V8_TYPED_ARRAY_GET_PRIVATE(Float64Array);
	return v8::Number::New(array->get(index));
}

v8::Handle<v8::Value> V8Uint8ClampedArray::indexedPropertyCustomGetter(unsigned int index, const v8::AccessorInfo &info) {
	V8_TYPED_ARRAY_GET_PRIVATE(Uint8ClampedArray);
	return v8::Uint32::New(array->get(index));
}

}
}