#ifndef V8ELEMENT_H_B55C09NB
#define V8ELEMENT_H_B55C09NB

#include "V8DOM.h"
#include "V8Node.h"

namespace uscxml {
	
	class V8Element {
	public:
	  static v8::Handle<v8::Value> tagNameAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) { assert(false); return v8::Undefined(); }

	  static v8::Handle<v8::Value> getAttributeCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> setAttributeCallback(const v8::Arguments& args);
	  static v8::Handle<v8::Value> removeAttributeCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> getAttributeNodeCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> setAttributeNodeCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> removeAttributeNodeCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> getElementsByTagNameCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> getAttributeNSCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> setAttributeNSCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> removeAttributeNSCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> getElementsByTagNameNSCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> getAttributeNodeNSCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> setAttributeNodeNSCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> hasAttributeCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> hasAttributeNSCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }

	  V8_DESTRUCTOR(Arabica::DOM::Element<std::string>);

		static v8::Persistent<v8::FunctionTemplate> Tmpl;
		static v8::Handle<v8::FunctionTemplate> getTmpl() {
		  if (Tmpl.IsEmpty()) {
		    v8::Handle<v8::FunctionTemplate> tmpl = v8::FunctionTemplate::New();
		    tmpl->SetClassName(v8::String::New("Element"));
		    tmpl->ReadOnlyPrototype();

		    v8::Local<v8::ObjectTemplate> instance = tmpl->InstanceTemplate();
		    v8::Local<v8::ObjectTemplate> prototype = tmpl->PrototypeTemplate();
		    instance->SetInternalFieldCount(2);

		    instance->SetAccessor(v8::String::NewSymbol("tagName"), V8Element::tagNameAttrGetter, 0,
		                          v8::External::New(0), static_cast<v8::AccessControl>(v8::DEFAULT), static_cast<v8::PropertyAttribute>(v8::None));

		    prototype->Set(v8::String::NewSymbol("getAttribute"),
		                   v8::FunctionTemplate::New(V8Element::getAttributeCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("setAttribute"),
		                   v8::FunctionTemplate::New(V8Element::setAttributeCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("removeAttribute"),
		                   v8::FunctionTemplate::New(V8Element::removeAttributeCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("getAttributeNode"),
		                   v8::FunctionTemplate::New(V8Element::getAttributeNodeCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("setAttributeNode"),
		                   v8::FunctionTemplate::New(V8Element::setAttributeNodeCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("removeAttributeNode"),
		                   v8::FunctionTemplate::New(V8Element::removeAttributeNodeCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("getElementsByTagName"),
		                   v8::FunctionTemplate::New(V8Element::getElementsByTagNameCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("getAttributeNS"),
		                   v8::FunctionTemplate::New(V8Element::getAttributeNSCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("setAttributeNS"),
		                   v8::FunctionTemplate::New(V8Element::setAttributeNSCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("removeAttributeNS"),
		                   v8::FunctionTemplate::New(V8Element::removeAttributeNSCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("getElementsByTagNameNS"),
		                   v8::FunctionTemplate::New(V8Element::getElementsByTagNameNSCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("getAttributeNodeNS"),
		                   v8::FunctionTemplate::New(V8Element::getAttributeNodeNSCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("setAttributeNodeNS"),
		                   v8::FunctionTemplate::New(V8Element::setAttributeNodeNSCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("hasAttribute"),
		                   v8::FunctionTemplate::New(V8Element::hasAttributeCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("hasAttributeNS"),
		                   v8::FunctionTemplate::New(V8Element::hasAttributeNSCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));

		    tmpl->Inherit(V8Node::getTmpl());
		    Tmpl = v8::Persistent<v8::FunctionTemplate>::New(tmpl);
		  }
		  return Tmpl;
		}

	};
	
}


#endif /* end of include guard: V8ELEMENT_H_B55C09NB */
