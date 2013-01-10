#include "V8Element.h"
#include <DOM/Element.hpp>

namespace uscxml {

using namespace Arabica::DOM;

v8::Persistent<v8::FunctionTemplate> V8Element::Tmpl;

v8::Handle<v8::Value> V8Element::setAttributeCallback(const v8::Arguments& args) {
  ASSERT_ARGS2(args, IsString, IsString);
  v8::String::AsciiValue key(args[0]);
  v8::String::AsciiValue value(args[1]);

  v8::Local<v8::Object> self = args.Holder();
  Element<std::string>* elem = V8DOM::toClassPtr<Element<std::string> >(self->GetInternalField(0));
  V8DOM* dom = V8DOM::toClassPtr<V8DOM>(self->GetInternalField(1)); (void)dom;

  elem->setAttribute(*key, *value);

  return v8::Undefined();
}

}