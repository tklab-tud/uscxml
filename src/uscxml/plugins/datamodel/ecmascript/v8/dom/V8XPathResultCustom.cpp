#include "V8XPathResult.h"
#include "V8Node.h"

namespace Arabica {
namespace DOM {

v8::Handle<v8::Value> V8XPathResult::singleNodeValueCustomAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
  v8::Local<v8::Object> self = info.Holder();
  V8XPathResultPrivate* privData = V8DOM::toClassPtr<V8XPathResultPrivate >(self->GetInternalField(0));

  Arabica::DOM::Node<std::string>* retVal = new Arabica::DOM::Node<std::string>(privData->arabicaThis->asNodeSet()[0]);

  v8::Handle<v8::Function> retCtor = V8Node::getTmpl()->GetFunction();
  v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());
  
  struct V8Node::V8NodePrivate* retPrivData = new V8Node::V8NodePrivate();
  retPrivData->dom = privData->dom;
  retPrivData->arabicaThis = retVal;
  
  retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));
  
  retObj.MakeWeak(0, V8Node::jsDestructor);
  return retObj;
}

}
}