#include "V8DataView.h"

namespace Arabica {
namespace DOM {

v8::Persistent<v8::FunctionTemplate> V8DataView::Tmpl;

v8::Handle<v8::Value> V8DataView::getInt8Callback(const v8::Arguments& args) {
	if (args.Length() < 1)
		throw V8Exception("Wrong number of arguments in getInt8");

	v8::Local<v8::Object> self = args.Holder();
	struct V8DataViewPrivate* privData = V8DOM::toClassPtr<V8DataViewPrivate >(self->GetInternalField(0));
	unsigned long localByteOffset = args[0]->ToNumber()->Uint32Value();

	char retVal = privData->nativeObj->getInt8(localByteOffset);

	return v8::Number::New(retVal);
}

v8::Handle<v8::Value> V8DataView::getUint8Callback(const v8::Arguments& args) {
	if (args.Length() < 1)
		throw V8Exception("Wrong number of arguments in getUint8");

	v8::Local<v8::Object> self = args.Holder();
	struct V8DataViewPrivate* privData = V8DOM::toClassPtr<V8DataViewPrivate >(self->GetInternalField(0));
	unsigned long localByteOffset = args[0]->ToNumber()->Uint32Value();

	char retVal = privData->nativeObj->getUint8(localByteOffset);

	return v8::Number::New(retVal);
}

v8::Handle<v8::Value> V8DataView::getInt16Callback(const v8::Arguments& args) {
	if (args.Length() < 2)
		throw V8Exception("Wrong number of arguments in getInt16");

	v8::Local<v8::Object> self = args.Holder();
	struct V8DataViewPrivate* privData = V8DOM::toClassPtr<V8DataViewPrivate >(self->GetInternalField(0));
	unsigned long localByteOffset = args[0]->ToNumber()->Uint32Value();
	bool localLittleEndian = args[1]->ToBoolean()->BooleanValue();

	short retVal = privData->nativeObj->getInt16(localByteOffset, localLittleEndian);

	return v8::Number::New(retVal);
}

v8::Handle<v8::Value> V8DataView::getUint16Callback(const v8::Arguments& args) {
	if (args.Length() < 2)
		throw V8Exception("Wrong number of arguments in getUint16");

	v8::Local<v8::Object> self = args.Holder();
	struct V8DataViewPrivate* privData = V8DOM::toClassPtr<V8DataViewPrivate >(self->GetInternalField(0));
	unsigned long localByteOffset = args[0]->ToNumber()->Uint32Value();
	bool localLittleEndian = args[1]->ToBoolean()->BooleanValue();

	unsigned short retVal = privData->nativeObj->getUint16(localByteOffset, localLittleEndian);

	return v8::Number::New(retVal);
}

v8::Handle<v8::Value> V8DataView::getInt32Callback(const v8::Arguments& args) {
	if (args.Length() < 2)
		throw V8Exception("Wrong number of arguments in getInt32");

	v8::Local<v8::Object> self = args.Holder();
	struct V8DataViewPrivate* privData = V8DOM::toClassPtr<V8DataViewPrivate >(self->GetInternalField(0));
	unsigned long localByteOffset = args[0]->ToNumber()->Uint32Value();
	bool localLittleEndian = args[1]->ToBoolean()->BooleanValue();

	long retVal = privData->nativeObj->getInt32(localByteOffset, localLittleEndian);

	return v8::Number::New(retVal);
}

v8::Handle<v8::Value> V8DataView::getUint32Callback(const v8::Arguments& args) {
	if (args.Length() < 2)
		throw V8Exception("Wrong number of arguments in getUint32");

	v8::Local<v8::Object> self = args.Holder();
	struct V8DataViewPrivate* privData = V8DOM::toClassPtr<V8DataViewPrivate >(self->GetInternalField(0));
	unsigned long localByteOffset = args[0]->ToNumber()->Uint32Value();
	bool localLittleEndian = args[1]->ToBoolean()->BooleanValue();

	unsigned long retVal = privData->nativeObj->getUint32(localByteOffset, localLittleEndian);

	return v8::Number::New(retVal);
}

v8::Handle<v8::Value> V8DataView::getFloat32Callback(const v8::Arguments& args) {
	if (args.Length() < 2)
		throw V8Exception("Wrong number of arguments in getFloat32");

	v8::Local<v8::Object> self = args.Holder();
	struct V8DataViewPrivate* privData = V8DOM::toClassPtr<V8DataViewPrivate >(self->GetInternalField(0));
	unsigned long localByteOffset = args[0]->ToNumber()->Uint32Value();
	bool localLittleEndian = args[1]->ToBoolean()->BooleanValue();

	float retVal = privData->nativeObj->getFloat32(localByteOffset, localLittleEndian);

	return v8::Number::New(retVal);
}

v8::Handle<v8::Value> V8DataView::getFloat64Callback(const v8::Arguments& args) {
	if (args.Length() < 2)
		throw V8Exception("Wrong number of arguments in getFloat64");

	v8::Local<v8::Object> self = args.Holder();
	struct V8DataViewPrivate* privData = V8DOM::toClassPtr<V8DataViewPrivate >(self->GetInternalField(0));
	unsigned long localByteOffset = args[0]->ToNumber()->Uint32Value();
	bool localLittleEndian = args[1]->ToBoolean()->BooleanValue();

	double retVal = privData->nativeObj->getFloat64(localByteOffset, localLittleEndian);

	return v8::Number::New(retVal);
}

v8::Handle<v8::Value> V8DataView::setInt8Callback(const v8::Arguments& args) {
	if (args.Length() < 2)
		throw V8Exception("Wrong number of arguments in setInt8");

	v8::Local<v8::Object> self = args.Holder();
	struct V8DataViewPrivate* privData = V8DOM::toClassPtr<V8DataViewPrivate >(self->GetInternalField(0));
	unsigned long localByteOffset = args[0]->ToNumber()->Uint32Value();
	char localValue = args[1]->ToNumber()->Int32Value();

	privData->nativeObj->setInt8(localByteOffset, localValue);

	return v8::Undefined();
}

v8::Handle<v8::Value> V8DataView::setUint8Callback(const v8::Arguments& args) {
	if (args.Length() < 2)
		throw V8Exception("Wrong number of arguments in setUint8");

	v8::Local<v8::Object> self = args.Holder();
	struct V8DataViewPrivate* privData = V8DOM::toClassPtr<V8DataViewPrivate >(self->GetInternalField(0));
	unsigned long localByteOffset = args[0]->ToNumber()->Uint32Value();
	unsigned char localValue = args[1]->ToNumber()->Uint32Value();

	privData->nativeObj->setUint8(localByteOffset, localValue);

	return v8::Undefined();
}

v8::Handle<v8::Value> V8DataView::setInt16Callback(const v8::Arguments& args) {
	if (args.Length() < 3)
		throw V8Exception("Wrong number of arguments in setInt16");

	v8::Local<v8::Object> self = args.Holder();
	struct V8DataViewPrivate* privData = V8DOM::toClassPtr<V8DataViewPrivate >(self->GetInternalField(0));
	unsigned long localByteOffset = args[0]->ToNumber()->Uint32Value();
	short localValue = args[1]->ToNumber()->Int32Value();
	bool localLittleEndian = args[2]->ToBoolean()->BooleanValue();

	privData->nativeObj->setInt16(localByteOffset, localValue, localLittleEndian);

	return v8::Undefined();
}

v8::Handle<v8::Value> V8DataView::setUint16Callback(const v8::Arguments& args) {
	if (args.Length() < 3)
		throw V8Exception("Wrong number of arguments in setUint16");

	v8::Local<v8::Object> self = args.Holder();
	struct V8DataViewPrivate* privData = V8DOM::toClassPtr<V8DataViewPrivate >(self->GetInternalField(0));
	unsigned long localByteOffset = args[0]->ToNumber()->Uint32Value();
	unsigned short localValue = args[1]->ToNumber()->Uint32Value();
	bool localLittleEndian = args[2]->ToBoolean()->BooleanValue();

	privData->nativeObj->setUint16(localByteOffset, localValue, localLittleEndian);

	return v8::Undefined();
}

v8::Handle<v8::Value> V8DataView::setInt32Callback(const v8::Arguments& args) {
	if (args.Length() < 3)
		throw V8Exception("Wrong number of arguments in setInt32");

	v8::Local<v8::Object> self = args.Holder();
	struct V8DataViewPrivate* privData = V8DOM::toClassPtr<V8DataViewPrivate >(self->GetInternalField(0));
	unsigned long localByteOffset = args[0]->ToNumber()->Uint32Value();
	long localValue = args[1]->ToNumber()->Int32Value();
	bool localLittleEndian = args[2]->ToBoolean()->BooleanValue();

	privData->nativeObj->setInt32(localByteOffset, localValue, localLittleEndian);

	return v8::Undefined();
}

v8::Handle<v8::Value> V8DataView::setUint32Callback(const v8::Arguments& args) {
	if (args.Length() < 3)
		throw V8Exception("Wrong number of arguments in setUint32");

	v8::Local<v8::Object> self = args.Holder();
	struct V8DataViewPrivate* privData = V8DOM::toClassPtr<V8DataViewPrivate >(self->GetInternalField(0));
	unsigned long localByteOffset = args[0]->ToNumber()->Uint32Value();
	unsigned long localValue = args[1]->ToNumber()->Uint32Value();
	bool localLittleEndian = args[2]->ToBoolean()->BooleanValue();

	privData->nativeObj->setUint32(localByteOffset, localValue, localLittleEndian);

	return v8::Undefined();
}

v8::Handle<v8::Value> V8DataView::setFloat32Callback(const v8::Arguments& args) {
	if (args.Length() < 3)
		throw V8Exception("Wrong number of arguments in setFloat32");

	v8::Local<v8::Object> self = args.Holder();
	struct V8DataViewPrivate* privData = V8DOM::toClassPtr<V8DataViewPrivate >(self->GetInternalField(0));
	unsigned long localByteOffset = args[0]->ToNumber()->Uint32Value();
	float localValue = args[1]->ToNumber()->Value();
	bool localLittleEndian = args[2]->ToBoolean()->BooleanValue();

	privData->nativeObj->setFloat32(localByteOffset, localValue, localLittleEndian);

	return v8::Undefined();
}

v8::Handle<v8::Value> V8DataView::setFloat64Callback(const v8::Arguments& args) {
	if (args.Length() < 3)
		throw V8Exception("Wrong number of arguments in setFloat64");

	v8::Local<v8::Object> self = args.Holder();
	struct V8DataViewPrivate* privData = V8DOM::toClassPtr<V8DataViewPrivate >(self->GetInternalField(0));
	unsigned long localByteOffset = args[0]->ToNumber()->Uint32Value();
	double localValue = args[1]->ToNumber()->Value();
	bool localLittleEndian = args[2]->ToBoolean()->BooleanValue();

	privData->nativeObj->setFloat64(localByteOffset, localValue, localLittleEndian);

	return v8::Undefined();
}

bool V8DataView::hasInstance(v8::Handle<v8::Value> value) {
	return getTmpl()->HasInstance(value);
}

}
}
