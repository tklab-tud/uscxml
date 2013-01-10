#ifndef V8NODE_H_9VGQMJNI
#define V8NODE_H_9VGQMJNI

#include "V8DOM.h"

namespace uscxml {

	class V8Node {
	public:
	  static v8::Handle<v8::Value> nodeNameAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> nodeValueAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> nodeTypeAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> parentNodeAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> childNodesAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> firstChildAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> lastChildAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> previousSiblingAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> nextSiblingAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> attributesAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> ownerDocumentAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> namespaceURIAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> prefixAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> localNameAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> baseURIAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> textContentAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> parentElementAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) { assert(false); return v8::Undefined(); }

	  static void nodeValueAttrSetter(v8::Local<v8::String> property, v8::Local<v8::Value> value, const v8::AccessorInfo& info) { }
	  static void prefixAttrSetter(v8::Local<v8::String> property, v8::Local<v8::Value> value, const v8::AccessorInfo& info) { }
	  static void textContentAttrSetter(v8::Local<v8::String> property, v8::Local<v8::Value> value, const v8::AccessorInfo& info) { }

	  static v8::Handle<v8::Value> insertBeforeCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> replaceChildCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> removeChildCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> appendChildCallback(const v8::Arguments& args);
	  static v8::Handle<v8::Value> hasChildNodesCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> cloneNodeCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> normalizeCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> isSupportedCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> hasAttributesCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> lookupPrefixCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> isDefaultNamespaceCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> lookupNamespaceURICallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> addEventListenerCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }
	  static v8::Handle<v8::Value> removeEventListenerCallback(const v8::Arguments& args) { assert(false); return v8::Undefined(); }

	  V8_DESTRUCTOR(Arabica::DOM::Node<std::string>);

		static v8::Persistent<v8::FunctionTemplate> Tmpl;
		static v8::Handle<v8::FunctionTemplate> getTmpl() {
		  if (Tmpl.IsEmpty()) {
		    v8::Handle<v8::FunctionTemplate> tmpl = v8::FunctionTemplate::New();
		    tmpl->SetClassName(v8::String::New("Node"));
		    tmpl->ReadOnlyPrototype();

		    v8::Local<v8::ObjectTemplate> instance = tmpl->InstanceTemplate();
		    v8::Local<v8::ObjectTemplate> prototype = tmpl->PrototypeTemplate();
		    instance->SetInternalFieldCount(2);

		    instance->SetAccessor(v8::String::NewSymbol("nodeName"), V8Node::nodeNameAttrGetter, 0,
		                          v8::External::New(0), static_cast<v8::AccessControl>(v8::DEFAULT), static_cast<v8::PropertyAttribute>(v8::None));
		    instance->SetAccessor(v8::String::NewSymbol("nodeValue"), V8Node::nodeValueAttrGetter, V8Node::nodeValueAttrSetter,
		                          v8::External::New(0), static_cast<v8::AccessControl>(v8::DEFAULT), static_cast<v8::PropertyAttribute>(v8::None));
		    instance->SetAccessor(v8::String::NewSymbol("nodeType"), V8Node::nodeTypeAttrGetter, 0,
		                          v8::External::New(0), static_cast<v8::AccessControl>(v8::DEFAULT), static_cast<v8::PropertyAttribute>(v8::None));
		    instance->SetAccessor(v8::String::NewSymbol("parentNode"), V8Node::parentNodeAttrGetter, 0,
		                          v8::External::New(0), static_cast<v8::AccessControl>(v8::DEFAULT), static_cast<v8::PropertyAttribute>(v8::None));
		    instance->SetAccessor(v8::String::NewSymbol("childNodes"), V8Node::childNodesAttrGetter, 0,
		                          v8::External::New(0), static_cast<v8::AccessControl>(v8::DEFAULT), static_cast<v8::PropertyAttribute>(v8::None));
		    instance->SetAccessor(v8::String::NewSymbol("firstChild"), V8Node::firstChildAttrGetter, 0,
		                          v8::External::New(0), static_cast<v8::AccessControl>(v8::DEFAULT), static_cast<v8::PropertyAttribute>(v8::None));
		    instance->SetAccessor(v8::String::NewSymbol("lastChild"), V8Node::lastChildAttrGetter, 0,
		                          v8::External::New(0), static_cast<v8::AccessControl>(v8::DEFAULT), static_cast<v8::PropertyAttribute>(v8::None));
		    instance->SetAccessor(v8::String::NewSymbol("previousSibling"), V8Node::previousSiblingAttrGetter, 0,
		                          v8::External::New(0), static_cast<v8::AccessControl>(v8::DEFAULT), static_cast<v8::PropertyAttribute>(v8::None));
		    instance->SetAccessor(v8::String::NewSymbol("nextSibling"), V8Node::nextSiblingAttrGetter, 0,
		                          v8::External::New(0), static_cast<v8::AccessControl>(v8::DEFAULT), static_cast<v8::PropertyAttribute>(v8::None));
		    instance->SetAccessor(v8::String::NewSymbol("attributes"), V8Node::attributesAttrGetter, 0,
		                          v8::External::New(0), static_cast<v8::AccessControl>(v8::DEFAULT), static_cast<v8::PropertyAttribute>(v8::None));
		    instance->SetAccessor(v8::String::NewSymbol("ownerDocument"), V8Node::ownerDocumentAttrGetter, 0,
		                          v8::External::New(0), static_cast<v8::AccessControl>(v8::DEFAULT), static_cast<v8::PropertyAttribute>(v8::None));
		    instance->SetAccessor(v8::String::NewSymbol("namespaceURI"), V8Node::namespaceURIAttrGetter, 0,
		                          v8::External::New(0), static_cast<v8::AccessControl>(v8::DEFAULT), static_cast<v8::PropertyAttribute>(v8::None));
		    instance->SetAccessor(v8::String::NewSymbol("prefix"), V8Node::prefixAttrGetter, V8Node::prefixAttrSetter,
		                          v8::External::New(0), static_cast<v8::AccessControl>(v8::DEFAULT), static_cast<v8::PropertyAttribute>(v8::None));
		    instance->SetAccessor(v8::String::NewSymbol("localName"), V8Node::localNameAttrGetter, 0,
		                          v8::External::New(0), static_cast<v8::AccessControl>(v8::DEFAULT), static_cast<v8::PropertyAttribute>(v8::None));
		    instance->SetAccessor(v8::String::NewSymbol("baseURI"), V8Node::baseURIAttrGetter, 0,
		                          v8::External::New(0), static_cast<v8::AccessControl>(v8::DEFAULT), static_cast<v8::PropertyAttribute>(v8::None));
		    instance->SetAccessor(v8::String::NewSymbol("textContent"), V8Node::textContentAttrGetter, V8Node::textContentAttrSetter,
		                          v8::External::New(0), static_cast<v8::AccessControl>(v8::DEFAULT), static_cast<v8::PropertyAttribute>(v8::None));
		    instance->SetAccessor(v8::String::NewSymbol("parentElement"), V8Node::parentElementAttrGetter, 0,
		                          v8::External::New(0), static_cast<v8::AccessControl>(v8::DEFAULT), static_cast<v8::PropertyAttribute>(v8::None));

		    prototype->Set(v8::String::NewSymbol("insertBefore"),
		                   v8::FunctionTemplate::New(V8Node::insertBeforeCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("replaceChild"),
		                   v8::FunctionTemplate::New(V8Node::replaceChildCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("removeChild"),
		                   v8::FunctionTemplate::New(V8Node::removeChildCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("appendChild"),
		                   v8::FunctionTemplate::New(V8Node::appendChildCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("hasChildNodes"),
		                   v8::FunctionTemplate::New(V8Node::hasChildNodesCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("cloneNode"),
		                   v8::FunctionTemplate::New(V8Node::cloneNodeCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("normalize"),
		                   v8::FunctionTemplate::New(V8Node::normalizeCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("isSupported"),
		                   v8::FunctionTemplate::New(V8Node::isSupportedCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("hasAttributes"),
		                   v8::FunctionTemplate::New(V8Node::hasAttributesCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("lookupPrefix"),
		                   v8::FunctionTemplate::New(V8Node::lookupPrefixCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("isDefaultNamespace"),
		                   v8::FunctionTemplate::New(V8Node::isDefaultNamespaceCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("lookupNamespaceURI"),
		                   v8::FunctionTemplate::New(V8Node::lookupNamespaceURICallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("addEventListener"),
		                   v8::FunctionTemplate::New(V8Node::addEventListenerCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));
		    prototype->Set(v8::String::NewSymbol("removeEventListener"),
		                   v8::FunctionTemplate::New(V8Node::removeEventListenerCallback, v8::Undefined()), static_cast<v8::PropertyAttribute>(v8::DontDelete));

		    tmpl->Set(v8::String::NewSymbol("ELEMENT_NODE"), v8::Integer::New(Arabica::DOM::Node_base::ELEMENT_NODE), v8::ReadOnly);
		      prototype->Set(v8::String::NewSymbol("ELEMENT_NODE"), v8::Integer::New(Arabica::DOM::Node_base::ELEMENT_NODE), v8::ReadOnly);
		    tmpl->Set(v8::String::NewSymbol("ATTRIBUTE_NODE"), v8::Integer::New(Arabica::DOM::Node_base::ATTRIBUTE_NODE), v8::ReadOnly);
		      prototype->Set(v8::String::NewSymbol("ATTRIBUTE_NODE"), v8::Integer::New(Arabica::DOM::Node_base::ATTRIBUTE_NODE), v8::ReadOnly);
		    tmpl->Set(v8::String::NewSymbol("TEXT_NODE"), v8::Integer::New(Arabica::DOM::Node_base::TEXT_NODE), v8::ReadOnly);
		      prototype->Set(v8::String::NewSymbol("TEXT_NODE"), v8::Integer::New(Arabica::DOM::Node_base::TEXT_NODE), v8::ReadOnly);
		    tmpl->Set(v8::String::NewSymbol("CDATA_SECTION_NODE"), v8::Integer::New(Arabica::DOM::Node_base::CDATA_SECTION_NODE), v8::ReadOnly);
		      prototype->Set(v8::String::NewSymbol("CDATA_SECTION_NODE"), v8::Integer::New(Arabica::DOM::Node_base::CDATA_SECTION_NODE), v8::ReadOnly);
		    tmpl->Set(v8::String::NewSymbol("ENTITY_REFERENCE_NODE"), v8::Integer::New(Arabica::DOM::Node_base::ENTITY_REFERENCE_NODE), v8::ReadOnly);
		      prototype->Set(v8::String::NewSymbol("ENTITY_REFERENCE_NODE"), v8::Integer::New(Arabica::DOM::Node_base::ENTITY_REFERENCE_NODE), v8::ReadOnly);
		    tmpl->Set(v8::String::NewSymbol("ENTITY_NODE"), v8::Integer::New(Arabica::DOM::Node_base::ENTITY_NODE), v8::ReadOnly);
		      prototype->Set(v8::String::NewSymbol("ENTITY_NODE"), v8::Integer::New(Arabica::DOM::Node_base::ENTITY_NODE), v8::ReadOnly);
		    tmpl->Set(v8::String::NewSymbol("PROCESSING_INSTRUCTION_NODE"), v8::Integer::New(Arabica::DOM::Node_base::PROCESSING_INSTRUCTION_NODE), v8::ReadOnly);
		      prototype->Set(v8::String::NewSymbol("PROCESSING_INSTRUCTION_NODE"), v8::Integer::New(Arabica::DOM::Node_base::PROCESSING_INSTRUCTION_NODE), v8::ReadOnly);
		    tmpl->Set(v8::String::NewSymbol("COMMENT_NODE"), v8::Integer::New(Arabica::DOM::Node_base::COMMENT_NODE), v8::ReadOnly);
		      prototype->Set(v8::String::NewSymbol("COMMENT_NODE"), v8::Integer::New(Arabica::DOM::Node_base::COMMENT_NODE), v8::ReadOnly);
		    tmpl->Set(v8::String::NewSymbol("DOCUMENT_NODE"), v8::Integer::New(Arabica::DOM::Node_base::DOCUMENT_NODE), v8::ReadOnly);
		      prototype->Set(v8::String::NewSymbol("DOCUMENT_NODE"), v8::Integer::New(Arabica::DOM::Node_base::DOCUMENT_NODE), v8::ReadOnly);
		    tmpl->Set(v8::String::NewSymbol("DOCUMENT_TYPE_NODE"), v8::Integer::New(Arabica::DOM::Node_base::DOCUMENT_TYPE_NODE), v8::ReadOnly);
		      prototype->Set(v8::String::NewSymbol("DOCUMENT_TYPE_NODE"), v8::Integer::New(Arabica::DOM::Node_base::DOCUMENT_TYPE_NODE), v8::ReadOnly);
		    tmpl->Set(v8::String::NewSymbol("DOCUMENT_FRAGMENT_NODE"), v8::Integer::New(Arabica::DOM::Node_base::DOCUMENT_FRAGMENT_NODE), v8::ReadOnly);
		      prototype->Set(v8::String::NewSymbol("DOCUMENT_FRAGMENT_NODE"), v8::Integer::New(Arabica::DOM::Node_base::DOCUMENT_FRAGMENT_NODE), v8::ReadOnly);
		    tmpl->Set(v8::String::NewSymbol("NOTATION_NODE"), v8::Integer::New(Arabica::DOM::Node_base::NOTATION_NODE), v8::ReadOnly);
		      prototype->Set(v8::String::NewSymbol("NOTATION_NODE"), v8::Integer::New(Arabica::DOM::Node_base::NOTATION_NODE), v8::ReadOnly);
		    tmpl->Set(v8::String::NewSymbol("MAX_TYPE"), v8::Integer::New(Arabica::DOM::Node_base::MAX_TYPE), v8::ReadOnly);
		      prototype->Set(v8::String::NewSymbol("MAX_TYPE"), v8::Integer::New(Arabica::DOM::Node_base::MAX_TYPE), v8::ReadOnly);

		    Tmpl = v8::Persistent<v8::FunctionTemplate>::New(tmpl);
		  }
		  return Tmpl;
		}

	};

}


#endif /* end of include guard: V8NODE_H_9VGQMJNI */
