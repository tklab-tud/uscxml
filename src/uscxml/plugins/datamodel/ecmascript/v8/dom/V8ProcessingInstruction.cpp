#include "V8Node.h"
#include "V8ProcessingInstruction.h"

namespace Arabica {
namespace DOM {

v8::Persistent<v8::FunctionTemplate> V8ProcessingInstruction::Tmpl;

v8::Handle<v8::Value> V8ProcessingInstruction::targetAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8ProcessingInstructionPrivate* privData = V8DOM::toClassPtr<V8ProcessingInstructionPrivate >(self->GetInternalField(0));

	return v8::String::New(privData->nativeObj->getTarget().c_str());
}

v8::Handle<v8::Value> V8ProcessingInstruction::dataAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8ProcessingInstructionPrivate* privData = V8DOM::toClassPtr<V8ProcessingInstructionPrivate >(self->GetInternalField(0));

	return v8::String::New(privData->nativeObj->getData().c_str());
}

void V8ProcessingInstruction::dataAttrSetter(v8::Local<v8::String> property, v8::Local<v8::Value> value, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8ProcessingInstructionPrivate* privData = V8DOM::toClassPtr<V8ProcessingInstructionPrivate >(self->GetInternalField(0));
	v8::String::AsciiValue localData(value);
	privData->nativeObj->setData(*localData);
}
bool V8ProcessingInstruction::hasInstance(v8::Handle<v8::Value> value) {
	return getTmpl()->HasInstance(value);
}

}
}
