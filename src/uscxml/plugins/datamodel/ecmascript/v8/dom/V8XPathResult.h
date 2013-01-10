#ifndef V8XPATHRESULT_HPP_AYZD0IRH
#define V8XPATHRESULT_HPP_AYZD0IRH

#include "V8DOM.h"

namespace uscxml {
  class V8XPathResult {
  public:
    static v8::Handle<v8::Value> resultTypeAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) { assert(false); return v8::Undefined(); }
    static v8::Handle<v8::Value> numberValueAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) { assert(false); return v8::Undefined(); }
    static v8::Handle<v8::Value> stringValueAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) { assert(false); return v8::Undefined(); }
    static v8::Handle<v8::Value> booleanValueAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) { assert(false); return v8::Undefined(); }
    static v8::Handle<v8::Value> singleNodeAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) { assert(false); return v8::Undefined(); }
    static v8::Handle<v8::Value> invalidIteratorStateAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) { assert(false); return v8::Undefined(); }
    static v8::Handle<v8::Value> snapshotLengthAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) { assert(false); return v8::Undefined(); }

    static v8::Handle<v8::Value> iterateNextCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }
    static v8::Handle<v8::Value> snapshotItemCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }

    static v8::Handle<v8::Value> asNodeSetCallback(const v8::Arguments& args);
    static v8::Handle<v8::Value> asBoolCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }
    static v8::Handle<v8::Value> asStringCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }
    static v8::Handle<v8::Value> asNumberCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }

    V8_DESTRUCTOR(Arabica::XPath::XPathValue<std::string>);

    static v8::Persistent<v8::FunctionTemplate> Tmpl;
    static v8::Handle<v8::FunctionTemplate> getTmpl() {
      if (Tmpl.IsEmpty()) {
        v8::Handle<v8::FunctionTemplate> tmpl = v8::FunctionTemplate::New();
        tmpl->SetClassName(v8::String::New("XPathResult"));
        tmpl->ReadOnlyPrototype();

        v8::Local<v8::ObjectTemplate> instance = tmpl->InstanceTemplate();
        v8::Local<v8::ObjectTemplate> prototype = tmpl->PrototypeTemplate();
        instance->SetInternalFieldCount(2);

        instance->SetAccessor(v8::String::NewSymbol("resultType"), V8XPathResult::resultTypeAttrGetter, 0,
                              v8::External::New(0), static_cast<v8::AccessControl>(v8::DEFAULT), static_cast<v8::PropertyAttribute>(v8::None));
        instance->SetAccessor(v8::String::NewSymbol("numberValue"), V8XPathResult::numberValueAttrGetter, 0,
                              v8::External::New(0), static_cast<v8::AccessControl>(v8::DEFAULT), static_cast<v8::PropertyAttribute>(v8::None));
        instance->SetAccessor(v8::String::NewSymbol("stringValue"), V8XPathResult::stringValueAttrGetter, 0,
                              v8::External::New(0), static_cast<v8::AccessControl>(v8::DEFAULT), static_cast<v8::PropertyAttribute>(v8::None));
        instance->SetAccessor(v8::String::NewSymbol("booleanValue"), V8XPathResult::booleanValueAttrGetter, 0,
                              v8::External::New(0), static_cast<v8::AccessControl>(v8::DEFAULT), static_cast<v8::PropertyAttribute>(v8::None));
        instance->SetAccessor(v8::String::NewSymbol("singleNode"), V8XPathResult::singleNodeAttrGetter, 0,
                              v8::External::New(0), static_cast<v8::AccessControl>(v8::DEFAULT), static_cast<v8::PropertyAttribute>(v8::None));
        instance->SetAccessor(v8::String::NewSymbol("invalidIteratorState"), V8XPathResult::invalidIteratorStateAttrGetter, 0,
                              v8::External::New(0), static_cast<v8::AccessControl>(v8::DEFAULT), static_cast<v8::PropertyAttribute>(v8::None));
        instance->SetAccessor(v8::String::NewSymbol("snapshotLength"), V8XPathResult::snapshotLengthAttrGetter, 0,
                              v8::External::New(0), static_cast<v8::AccessControl>(v8::DEFAULT), static_cast<v8::PropertyAttribute>(v8::None));

        prototype->Set(v8::String::NewSymbol("iterateNext"),
                       v8::FunctionTemplate::New(V8XPathResult::iterateNextCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
        prototype->Set(v8::String::NewSymbol("snapshotItem"),
                       v8::FunctionTemplate::New(V8XPathResult::snapshotItemCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
        prototype->Set(v8::String::NewSymbol("asNodeSet"),
                       v8::FunctionTemplate::New(V8XPathResult::asNodeSetCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
        prototype->Set(v8::String::NewSymbol("asBool"),
                       v8::FunctionTemplate::New(V8XPathResult::asBoolCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
        prototype->Set(v8::String::NewSymbol("asString"),
                       v8::FunctionTemplate::New(V8XPathResult::asStringCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
        prototype->Set(v8::String::NewSymbol("asNumber"),
                       v8::FunctionTemplate::New(V8XPathResult::asNumberCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));

        Tmpl = v8::Persistent<v8::FunctionTemplate>::New(tmpl);
      }
      return Tmpl;
    }

  };
}


#endif /* end of include guard: V8XPATHRESULT_HPP_AYZD0IRH */
