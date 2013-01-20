#include "V8Entity.h"
#include "V8Node.h"

namespace Arabica {
namespace DOM {

  v8::Persistent<v8::FunctionTemplate> V8Entity::Tmpl;


  v8::Handle<v8::Value> V8Entity::publicIdAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
    v8::Local<v8::Object> self = info.Holder();
    V8EntityPrivate* privData = V8DOM::toClassPtr<V8EntityPrivate >(self->GetInternalField(0));

    return v8::String::New(privData->arabicaThis->getPublicId().c_str());
  }

  v8::Handle<v8::Value> V8Entity::systemIdAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
    v8::Local<v8::Object> self = info.Holder();
    V8EntityPrivate* privData = V8DOM::toClassPtr<V8EntityPrivate >(self->GetInternalField(0));

    return v8::String::New(privData->arabicaThis->getSystemId().c_str());
  }

  v8::Handle<v8::Value> V8Entity::notationNameAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
    v8::Local<v8::Object> self = info.Holder();
    V8EntityPrivate* privData = V8DOM::toClassPtr<V8EntityPrivate >(self->GetInternalField(0));

    return v8::String::New(privData->arabicaThis->getNotationName().c_str());
  }
  bool V8Entity::hasInstance(v8::Handle<v8::Value> value) {
    return getTmpl()->HasInstance(value);
  }

} 
} 
