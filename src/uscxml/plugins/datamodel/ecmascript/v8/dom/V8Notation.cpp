#include "V8Node.h"
#include "V8Notation.h"

namespace Arabica {
namespace DOM {

v8::Persistent<v8::FunctionTemplate> V8Notation::Tmpl;


v8::Handle<v8::Value> V8Notation::publicIdAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8NotationPrivate* privData = V8DOM::toClassPtr<V8NotationPrivate >(self->GetInternalField(0));

	return v8::String::New(privData->nativeObj->getPublicId().c_str());
}

v8::Handle<v8::Value> V8Notation::systemIdAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8NotationPrivate* privData = V8DOM::toClassPtr<V8NotationPrivate >(self->GetInternalField(0));

	return v8::String::New(privData->nativeObj->getSystemId().c_str());
}
bool V8Notation::hasInstance(v8::Handle<v8::Value> value) {
	return getTmpl()->HasInstance(value);
}

}
}
