#include "V8XPathResult.h"
#include "V8NodeSet.h"

namespace uscxml {

using namespace Arabica::DOM;
using namespace Arabica::XPath;

v8::Persistent<v8::FunctionTemplate> V8XPathResult::Tmpl;

v8::Handle<v8::Value> V8XPathResult::asNodeSetCallback(const v8::Arguments& args) {
  
  v8::Local<v8::Object> self = args.Holder();
  XPathValue<std::string>* xpathValue = V8DOM::toClassPtr<XPathValue<std::string> >(self->GetInternalField(0));
  V8DOM* dom = V8DOM::toClassPtr<V8DOM>(self->GetInternalField(1)); (void)dom;
  
  v8::Handle<v8::Function> nodeSetCtor = V8NodeSet::getTmpl()->GetFunction();
  v8::Persistent<v8::Object> nodeSetObj = v8::Persistent<v8::Object>::New(nodeSetCtor->NewInstance());
  
  Arabica::XPath::NodeSet<std::string>* nodeSet = new Arabica::XPath::NodeSet<std::string>(xpathValue->asNodeSet());
  
  nodeSetObj->SetInternalField(0, V8DOM::toExternal(nodeSet));
  nodeSetObj->SetInternalField(1, self->GetInternalField(1));
  
  nodeSetObj.MakeWeak(0, V8NodeSet::jsDestructor);
  return nodeSetObj;
  
}

}