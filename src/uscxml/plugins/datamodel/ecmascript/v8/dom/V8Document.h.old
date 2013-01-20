#ifndef V8DOCUMENT_H_COKK9O3L
#define V8DOCUMENT_H_COKK9O3L

#include "V8DOM.h"
#include "V8Node.h"

namespace uscxml {

	class V8Document {
	public:
	  static v8::Handle<v8::Value> doctypeAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> implementationAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> documentElementAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) { assert(false); return v8::Undefined(); }

	  static v8::Handle<v8::Value> createElementCallback(const v8::Arguments& args);
	  static v8::Handle<v8::Value> createDocumentFragmentCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> createTextNodeCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> createCommentCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> createCDATASectionCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> createProcessingInstructionCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> createAttributeCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> createEntityReferenceCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> getElementsByTagNameCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> importNodeCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> createElementNSCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> createAttributeNSCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> getElementsByTagNameNSCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> getElementByIdCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }

	  static v8::Handle<v8::Value> createEventCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }

	  static v8::Handle<v8::Value> createExpressionCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> createNSResolverCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> evaluateCallback(const v8::Arguments& args);

	  V8_DESTRUCTOR(Arabica::DOM::Document<std::string>);

		static v8::Persistent<v8::FunctionTemplate> Tmpl;
		static v8::Handle<v8::FunctionTemplate> getTmpl() {
		  if (Tmpl.IsEmpty()) {
		    v8::Handle<v8::FunctionTemplate> tmpl = v8::FunctionTemplate::New();
		    tmpl->SetClassName(v8::String::New("Document"));
		    tmpl->ReadOnlyPrototype();

		    v8::Local<v8::ObjectTemplate> instance = tmpl->InstanceTemplate();
		    v8::Local<v8::ObjectTemplate> prototype = tmpl->PrototypeTemplate();
		    instance->SetInternalFieldCount(2);

		    instance->SetAccessor(v8::String::NewSymbol("doctype"), V8Document::doctypeAttrGetter, 0,
		                          v8::External::New(0), static_cast<v8::AccessControl>(v8::DEFAULT), static_cast<v8::PropertyAttribute>(v8::None));
		    instance->SetAccessor(v8::String::NewSymbol("implementation"), V8Document::implementationAttrGetter, 0,
		                          v8::External::New(0), static_cast<v8::AccessControl>(v8::DEFAULT), static_cast<v8::PropertyAttribute>(v8::None));
		    instance->SetAccessor(v8::String::NewSymbol("documentElement"), V8Document::documentElementAttrGetter, 0,
		                          v8::External::New(0), static_cast<v8::AccessControl>(v8::DEFAULT), static_cast<v8::PropertyAttribute>(v8::None));

		    prototype->Set(v8::String::NewSymbol("createElement"),
		                   v8::FunctionTemplate::New(V8Document::createElementCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("createDocumentFragment"),
		                   v8::FunctionTemplate::New(V8Document::createDocumentFragmentCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("createTextNode"),
		                   v8::FunctionTemplate::New(V8Document::createTextNodeCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("createComment"),
		                   v8::FunctionTemplate::New(V8Document::createCommentCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("createCDATASection"),
		                   v8::FunctionTemplate::New(V8Document::createCDATASectionCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("createProcessingInstruction"),
		                   v8::FunctionTemplate::New(V8Document::createProcessingInstructionCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("createAttribute"),
		                   v8::FunctionTemplate::New(V8Document::createAttributeCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("createEntityReference"),
		                   v8::FunctionTemplate::New(V8Document::createEntityReferenceCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("getElementsByTagName"),
		                   v8::FunctionTemplate::New(V8Document::getElementsByTagNameCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("importNode"),
		                   v8::FunctionTemplate::New(V8Document::importNodeCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("createElementNS"),
		                   v8::FunctionTemplate::New(V8Document::createElementNSCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("createAttributeNS"),
		                   v8::FunctionTemplate::New(V8Document::createAttributeNSCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("getElementsByTagNameNS"),
		                   v8::FunctionTemplate::New(V8Document::getElementsByTagNameNSCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("getElementById"),
		                   v8::FunctionTemplate::New(V8Document::getElementByIdCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("createEvent"),
		                   v8::FunctionTemplate::New(V8Document::createEventCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("createExpression"),
		                   v8::FunctionTemplate::New(V8Document::createExpressionCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("createNSResolver"),
		                   v8::FunctionTemplate::New(V8Document::createNSResolverCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("evaluate"),
		                   v8::FunctionTemplate::New(V8Document::evaluateCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));

		    tmpl->Inherit(V8Node::getTmpl());
		    Tmpl = v8::Persistent<v8::FunctionTemplate>::New(tmpl);
		  }
		  return Tmpl;
		}

	};

}


#endif /* end of include guard: V8DOCUMENT_H_COKK9O3L */
