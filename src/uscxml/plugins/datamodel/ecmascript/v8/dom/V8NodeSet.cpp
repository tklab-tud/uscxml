#include "V8NodeSet.h"

namespace Arabica {
namespace DOM {

v8::Persistent<v8::FunctionTemplate> V8NodeSet::Tmpl;


v8::Handle<v8::Value> V8NodeSet::sizeAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8NodeSetPrivate* privData = V8DOM::toClassPtr<V8NodeSetPrivate >(self->GetInternalField(0));

	return v8::Integer::New(privData->arabicaThis->size());
}

v8::Handle<v8::Value> V8NodeSet::emptyAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8NodeSetPrivate* privData = V8DOM::toClassPtr<V8NodeSetPrivate >(self->GetInternalField(0));

	return v8::Boolean::New(privData->arabicaThis->empty());
}
v8::Handle<v8::Value> V8NodeSet::toDocumentOrderCallback(const v8::Arguments& args) {

	v8::Local<v8::Object> self = args.Holder();
	struct V8NodeSetPrivate* privData = V8DOM::toClassPtr<V8NodeSetPrivate >(self->GetInternalField(0));

	privData->arabicaThis->to_document_order();

	return v8::Undefined();
}

bool V8NodeSet::hasInstance(v8::Handle<v8::Value> value) {
	return getTmpl()->HasInstance(value);
}

}
}
