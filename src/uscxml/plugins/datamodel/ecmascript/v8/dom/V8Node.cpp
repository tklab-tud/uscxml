#include "V8Node.h"
#include <DOM/Node.hpp>

namespace uscxml {

using namespace Arabica::DOM;

v8::Persistent<v8::FunctionTemplate> V8Node::Tmpl;

v8::Handle<v8::Value> V8Node::appendChildCallback(const v8::Arguments& args) {
  assert(args.Length() == 1);
  assert(args[0]->IsObject());

  v8::Local<v8::Object> self = args.Holder();

  Node<std::string>* node = V8DOM::toClassPtr<Node<std::string> >(self->GetInternalField(0));
  Node<std::string>* childToAppend = V8DOM::toClassPtr<Node<std::string> >(args[0]->ToObject()->GetInternalField(0));
  node->appendChild(*childToAppend);
  
  return v8::Undefined();
}

}