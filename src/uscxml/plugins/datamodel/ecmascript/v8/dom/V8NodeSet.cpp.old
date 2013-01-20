#include "V8NodeSet.h"
#include "V8Element.h"
#include "V8Node.h"
#include <DOM/Node.hpp>

namespace uscxml {

using namespace Arabica::DOM;
using namespace Arabica::XPath;

v8::Persistent<v8::FunctionTemplate> V8NodeSet::Tmpl;


v8::Handle<v8::Value> V8NodeSet::indexGetter(uint32_t index, const v8::AccessorInfo &info) {
  v8::Local<v8::Object> self = info.Holder();

  NodeSet<std::string>* nodeSet = V8DOM::toClassPtr<NodeSet<std::string> >(self->GetInternalField(0));
  V8DOM* dom = V8DOM::toClassPtr<V8DOM>(self->GetInternalField(1)); (void)dom;
  
  if (nodeSet->size() >= index) {
    switch((*nodeSet)[index].getNodeType()) {
      case Node_base::ELEMENT_NODE: {
        v8::Handle<v8::Function> elementCtor = V8Element::getTmpl()->GetFunction();
        v8::Persistent<v8::Object> elementObj = v8::Persistent<v8::Object>::New(elementCtor->NewInstance());

        Element<std::string>* element = new Element<std::string>((*nodeSet)[index]);

        elementObj->SetInternalField(0, V8DOM::toExternal(element));
        elementObj->SetInternalField(1, self->GetInternalField(1));
        elementObj.MakeWeak(0, V8Element::jsDestructor);
        return elementObj;
      }
      default: {
        v8::Handle<v8::Function> nodeCtor = V8Node::getTmpl()->GetFunction();
        v8::Persistent<v8::Object> nodeObj = v8::Persistent<v8::Object>::New(nodeCtor->NewInstance());

        Node<std::string>* node = new Node<std::string>((*nodeSet)[index]);

        nodeObj->SetInternalField(0, V8DOM::toExternal(node));
        nodeObj->SetInternalField(1, self->GetInternalField(1));
        nodeObj.MakeWeak(0, V8Node::jsDestructor);
        return nodeObj;

      }
    }    
  }

  return v8::Undefined();
}

v8::Handle<v8::Value> V8NodeSet::lengthAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
  v8::Local<v8::Object> self = info.Holder();

  V8DOM* dom = V8DOM::toClassPtr<V8DOM>(self->GetInternalField(1)); (void)dom;
  NodeSet<std::string>* nodeSet = V8DOM::toClassPtr<NodeSet<std::string> >(self->GetInternalField(1));

  return v8::Integer::New(nodeSet->size());
}

}