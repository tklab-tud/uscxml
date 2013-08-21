#include "V8Storage.h"

namespace Arabica {
namespace DOM {

v8::Persistent<v8::FunctionTemplate> V8Storage::Tmpl;


v8::Handle<v8::Value> V8Storage::lengthAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8StoragePrivate* privData = V8DOM::toClassPtr<V8StoragePrivate >(self->GetInternalField(0));

	return v8::Integer::New(privData->nativeObj->getLength());
}
v8::Handle<v8::Value> V8Storage::keyCallback(const v8::Arguments& args) {
	if (args.Length() < 1)
		throw V8Exception("Wrong number of arguments in key");

	v8::Local<v8::Object> self = args.Holder();
	struct V8StoragePrivate* privData = V8DOM::toClassPtr<V8StoragePrivate >(self->GetInternalField(0));
	unsigned long localIndex = args[0]->ToNumber()->Uint32Value();

	std::string retVal = privData->nativeObj->key(localIndex);

	return v8::String::New(retVal.c_str());
}

v8::Handle<v8::Value> V8Storage::getItemCallback(const v8::Arguments& args) {
	if (args.Length() < 1)
		throw V8Exception("Wrong number of arguments in getItem");

	v8::Local<v8::Object> self = args.Holder();
	struct V8StoragePrivate* privData = V8DOM::toClassPtr<V8StoragePrivate >(self->GetInternalField(0));
	v8::String::AsciiValue localKey(args[0]);

	std::string retVal = privData->nativeObj->getItem(*localKey);

	return v8::String::New(retVal.c_str());
}

v8::Handle<v8::Value> V8Storage::setItemCallback(const v8::Arguments& args) {
	if (args.Length() < 2)
		throw V8Exception("Wrong number of arguments in setItem");

	v8::Local<v8::Object> self = args.Holder();
	struct V8StoragePrivate* privData = V8DOM::toClassPtr<V8StoragePrivate >(self->GetInternalField(0));
	v8::String::AsciiValue localKey(args[0]);
	v8::String::AsciiValue localValue(args[1]);

	privData->nativeObj->setItem(*localKey, *localValue);

	return v8::Undefined();
}

v8::Handle<v8::Value> V8Storage::removeItemCallback(const v8::Arguments& args) {
	if (args.Length() < 1)
		throw V8Exception("Wrong number of arguments in removeItem");

	v8::Local<v8::Object> self = args.Holder();
	struct V8StoragePrivate* privData = V8DOM::toClassPtr<V8StoragePrivate >(self->GetInternalField(0));
	v8::String::AsciiValue localKey(args[0]);

	privData->nativeObj->removeItem(*localKey);

	return v8::Undefined();
}

v8::Handle<v8::Value> V8Storage::clearCallback(const v8::Arguments& args) {

	v8::Local<v8::Object> self = args.Holder();
	struct V8StoragePrivate* privData = V8DOM::toClassPtr<V8StoragePrivate >(self->GetInternalField(0));

	privData->nativeObj->clear();

	return v8::Undefined();
}

bool V8Storage::hasInstance(v8::Handle<v8::Value> value) {
	return getTmpl()->HasInstance(value);
}

}
}
