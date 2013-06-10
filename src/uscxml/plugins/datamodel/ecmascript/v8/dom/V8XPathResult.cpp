#include "V8NodeSet.h"
#include "V8XPathResult.h"

namespace Arabica {
namespace DOM {

  v8::Persistent<v8::FunctionTemplate> V8XPathResult::Tmpl;


  v8::Handle<v8::Value> V8XPathResult::numberValueAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
    v8::Local<v8::Object> self = info.Holder();
    struct V8XPathResultPrivate* privData = V8DOM::toClassPtr<V8XPathResultPrivate >(self->GetInternalField(0));

    return v8::Number::New(privData->nativeObj->asNumber());
  }

  v8::Handle<v8::Value> V8XPathResult::stringValueAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
    v8::Local<v8::Object> self = info.Holder();
    struct V8XPathResultPrivate* privData = V8DOM::toClassPtr<V8XPathResultPrivate >(self->GetInternalField(0));

    return v8::String::New(privData->nativeObj->asString().c_str());
  }

  v8::Handle<v8::Value> V8XPathResult::booleanValueAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
    v8::Local<v8::Object> self = info.Holder();
    struct V8XPathResultPrivate* privData = V8DOM::toClassPtr<V8XPathResultPrivate >(self->GetInternalField(0));

    return v8::Boolean::New(privData->nativeObj->asBool());
  }
  v8::Handle<v8::Value> V8XPathResult::asNodeSetCallback(const v8::Arguments& args) {

    v8::Local<v8::Object> self = args.Holder();
    struct V8XPathResultPrivate* privData = V8DOM::toClassPtr<V8XPathResultPrivate >(self->GetInternalField(0));

    Arabica::XPath::NodeSet<std::string>* retVal = new Arabica::XPath::NodeSet<std::string>(privData->nativeObj->asNodeSet());
    v8::Handle<v8::Function> retCtor = V8NodeSet::getTmpl()->GetFunction();
    v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

    struct V8NodeSet::V8NodeSetPrivate* retPrivData = new V8NodeSet::V8NodeSetPrivate();
    retPrivData->dom = privData->dom;
    retPrivData->nativeObj = retVal;

    retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));

    retObj.MakeWeak(0, V8NodeSet::jsDestructor);
    return retObj;

  }

  v8::Handle<v8::Value> V8XPathResult::asBoolCallback(const v8::Arguments& args) {

    v8::Local<v8::Object> self = args.Holder();
    struct V8XPathResultPrivate* privData = V8DOM::toClassPtr<V8XPathResultPrivate >(self->GetInternalField(0));

    bool retVal = privData->nativeObj->asBool();

    return v8::Boolean::New(retVal);
  }

  v8::Handle<v8::Value> V8XPathResult::asStringCallback(const v8::Arguments& args) {

    v8::Local<v8::Object> self = args.Holder();
    struct V8XPathResultPrivate* privData = V8DOM::toClassPtr<V8XPathResultPrivate >(self->GetInternalField(0));

    std::string retVal = privData->nativeObj->asString();

    return v8::String::New(retVal.c_str());
  }

  v8::Handle<v8::Value> V8XPathResult::asNumberCallback(const v8::Arguments& args) {

    v8::Local<v8::Object> self = args.Holder();
    struct V8XPathResultPrivate* privData = V8DOM::toClassPtr<V8XPathResultPrivate >(self->GetInternalField(0));

    double retVal = privData->nativeObj->asNumber();

    return v8::Number::New(retVal);
  }

  bool V8XPathResult::hasInstance(v8::Handle<v8::Value> value) {
    return getTmpl()->HasInstance(value);
  }

} 
} 
