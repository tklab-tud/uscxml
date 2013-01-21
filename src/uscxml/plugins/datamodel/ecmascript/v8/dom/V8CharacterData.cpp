#include "V8CharacterData.h"
#include "V8Node.h"

namespace Arabica {
namespace DOM {

v8::Persistent<v8::FunctionTemplate> V8CharacterData::Tmpl;


v8::Handle<v8::Value> V8CharacterData::dataAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8CharacterDataPrivate* privData = V8DOM::toClassPtr<V8CharacterDataPrivate >(self->GetInternalField(0));

	return v8::String::New(privData->nativeObj->getData().c_str());
}

void V8CharacterData::dataAttrSetter(v8::Local<v8::String> property, v8::Local<v8::Value> value, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8CharacterDataPrivate* privData = V8DOM::toClassPtr<V8CharacterDataPrivate >(self->GetInternalField(0));
	v8::String::AsciiValue localData(value);
	privData->nativeObj->setData(*localData);
}

v8::Handle<v8::Value> V8CharacterData::lengthAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8CharacterDataPrivate* privData = V8DOM::toClassPtr<V8CharacterDataPrivate >(self->GetInternalField(0));

	return v8::Integer::New(privData->nativeObj->getLength());
}
v8::Handle<v8::Value> V8CharacterData::substringDataCallback(const v8::Arguments& args) {
	if (args.Length() < 2)
		throw V8Exception("Wrong number of arguments in substringData");

	v8::Local<v8::Object> self = args.Holder();
	struct V8CharacterDataPrivate* privData = V8DOM::toClassPtr<V8CharacterDataPrivate >(self->GetInternalField(0));
	unsigned long localOffset = args[0]->ToNumber()->Uint32Value();
	unsigned long localCount = args[1]->ToNumber()->Uint32Value();

	std::string retVal = privData->nativeObj->substringData(localOffset, localCount);

	return v8::String::New(retVal.c_str());
}

v8::Handle<v8::Value> V8CharacterData::appendDataCallback(const v8::Arguments& args) {
	if (args.Length() < 1)
		throw V8Exception("Wrong number of arguments in appendData");

	v8::Local<v8::Object> self = args.Holder();
	struct V8CharacterDataPrivate* privData = V8DOM::toClassPtr<V8CharacterDataPrivate >(self->GetInternalField(0));
	v8::String::AsciiValue localArg(args[0]);

	privData->nativeObj->appendData(*localArg);

	return v8::Undefined();
}

v8::Handle<v8::Value> V8CharacterData::insertDataCallback(const v8::Arguments& args) {
	if (args.Length() < 2)
		throw V8Exception("Wrong number of arguments in insertData");

	v8::Local<v8::Object> self = args.Holder();
	struct V8CharacterDataPrivate* privData = V8DOM::toClassPtr<V8CharacterDataPrivate >(self->GetInternalField(0));
	unsigned long localOffset = args[0]->ToNumber()->Uint32Value();
	v8::String::AsciiValue localArg(args[1]);

	privData->nativeObj->insertData(localOffset, *localArg);

	return v8::Undefined();
}

v8::Handle<v8::Value> V8CharacterData::deleteDataCallback(const v8::Arguments& args) {
	if (args.Length() < 2)
		throw V8Exception("Wrong number of arguments in deleteData");

	v8::Local<v8::Object> self = args.Holder();
	struct V8CharacterDataPrivate* privData = V8DOM::toClassPtr<V8CharacterDataPrivate >(self->GetInternalField(0));
	unsigned long localOffset = args[0]->ToNumber()->Uint32Value();
	unsigned long localCount = args[1]->ToNumber()->Uint32Value();

	privData->nativeObj->deleteData(localOffset, localCount);

	return v8::Undefined();
}

v8::Handle<v8::Value> V8CharacterData::replaceDataCallback(const v8::Arguments& args) {
	if (args.Length() < 3)
		throw V8Exception("Wrong number of arguments in replaceData");

	v8::Local<v8::Object> self = args.Holder();
	struct V8CharacterDataPrivate* privData = V8DOM::toClassPtr<V8CharacterDataPrivate >(self->GetInternalField(0));
	unsigned long localOffset = args[0]->ToNumber()->Uint32Value();
	unsigned long localCount = args[1]->ToNumber()->Uint32Value();
	v8::String::AsciiValue localArg(args[2]);

	privData->nativeObj->replaceData(localOffset, localCount, *localArg);

	return v8::Undefined();
}

bool V8CharacterData::hasInstance(v8::Handle<v8::Value> value) {
	return getTmpl()->HasInstance(value);
}

}
}
