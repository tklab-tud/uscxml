#ifndef V8NODESET_HPP_WKKXJ1RD
#define V8NODESET_HPP_WKKXJ1RD

#include "V8DOM.h"

namespace uscxml {

	class V8NodeSet {
	public:
		static v8::Handle<v8::Value> indexGetter(uint32_t index, const v8::AccessorInfo &info);
		static v8::Handle<v8::Value> indexSetter(uint32_t index, v8::Local<v8::Value> value, const v8::AccessorInfo &info) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> lengthAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info);

	  V8_DESTRUCTOR(Arabica::XPath::NodeSet<std::string>);

		static v8::Persistent<v8::FunctionTemplate> Tmpl;
		static v8::Handle<v8::FunctionTemplate> getTmpl() {
		  if (Tmpl.IsEmpty()) {
		    v8::Handle<v8::FunctionTemplate> tmpl = v8::FunctionTemplate::New();
		    tmpl->SetClassName(v8::String::New("NodeSet"));
		    tmpl->ReadOnlyPrototype();

		    v8::Local<v8::ObjectTemplate> instance = tmpl->InstanceTemplate();
		//    v8::Local<v8::ObjectTemplate> prototype = tmpl->PrototypeTemplate();
		    instance->SetInternalFieldCount(2);

		    instance->SetIndexedPropertyHandler(V8NodeSet::indexGetter, V8NodeSet::indexSetter);

		    instance->SetAccessor(v8::String::NewSymbol("length"), V8NodeSet::lengthAttrGetter, 0,
		                          v8::External::New(0), static_cast<v8::AccessControl>(v8::DEFAULT), static_cast<v8::PropertyAttribute>(v8::None));

		    Tmpl = v8::Persistent<v8::FunctionTemplate>::New(tmpl);
		  }
		  return Tmpl;
		}

	};

}

#endif /* end of include guard: V8NODESET_HPP_WKKXJ1RD */
