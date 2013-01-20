#ifndef JSCNODE_H_6BAK1S3C
#define JSCNODE_H_6BAK1S3C

#include "JSCDOM.h"

namespace uscxml {

	class JSCNode {
	public:
	  static JSValueRef nodeNameAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) { assert(false); return JSValueMakeUndefined(ctx); }
	  static JSValueRef nodeValueAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) { assert(false); return JSValueMakeUndefined(ctx); }
	  static JSValueRef nodeTypeAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) { assert(false); return JSValueMakeUndefined(ctx); }
	  static JSValueRef parentNodeAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) { assert(false); return JSValueMakeUndefined(ctx); }
	  static JSValueRef childNodesAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) { assert(false); return JSValueMakeUndefined(ctx); }
	  static JSValueRef firstChildAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) { assert(false); return JSValueMakeUndefined(ctx); }
	  static JSValueRef lastChildAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) { assert(false); return JSValueMakeUndefined(ctx); }
	  static JSValueRef previousSiblingAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) { assert(false); return JSValueMakeUndefined(ctx); }
	  static JSValueRef nextSiblingAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) { assert(false); return JSValueMakeUndefined(ctx); }
	  static JSValueRef attributesAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) { assert(false); return JSValueMakeUndefined(ctx); }
	  static JSValueRef ownerDocumentAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) { assert(false); return JSValueMakeUndefined(ctx); }
	  static JSValueRef namespaceURIAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) { assert(false); return JSValueMakeUndefined(ctx); }
	  static JSValueRef prefixAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) { assert(false); return JSValueMakeUndefined(ctx); }
	  static JSValueRef localNameAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) { assert(false); return JSValueMakeUndefined(ctx); }
	  static JSValueRef baseURIAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) { assert(false); return JSValueMakeUndefined(ctx); }
	  static JSValueRef textContentAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) { assert(false); return JSValueMakeUndefined(ctx); }
	  static JSValueRef parentElementAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) { assert(false); return JSValueMakeUndefined(ctx); }

	  static bool nodeValueAttrSetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef value, JSValueRef* exception) { return false; }
	  static bool prefixAttrSetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef value, JSValueRef* exception) { return false; }
	  static bool textContentAttrSetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef value, JSValueRef* exception) { return false; }

	  static JSValueRef insertBeforeCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) { assert(false); return JSValueMakeUndefined(ctx); }
	  static JSValueRef replaceChildCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) { assert(false); return JSValueMakeUndefined(ctx); }
	  static JSValueRef removeChildCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) { assert(false); return JSValueMakeUndefined(ctx); }
	  static JSValueRef appendChildCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) { assert(false); return JSValueMakeUndefined(ctx); }
	  static JSValueRef hasChildNodesCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) { assert(false); return JSValueMakeUndefined(ctx); }
	  static JSValueRef cloneNodeCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) { assert(false); return JSValueMakeUndefined(ctx); }
	  static JSValueRef normalizeCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) { assert(false); return JSValueMakeUndefined(ctx); }
	  static JSValueRef isSupportedCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) { assert(false); return JSValueMakeUndefined(ctx); }
	  static JSValueRef hasAttributesCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) { assert(false); return JSValueMakeUndefined(ctx); }
	  static JSValueRef lookupPrefixCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) { assert(false); return JSValueMakeUndefined(ctx); }
	  static JSValueRef isDefaultNamespaceCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) { assert(false); return JSValueMakeUndefined(ctx); }
	  static JSValueRef lookupNamespaceURICallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) { assert(false); return JSValueMakeUndefined(ctx); }
	  static JSValueRef addEventListenerCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) { assert(false); return JSValueMakeUndefined(ctx); }
	  static JSValueRef removeEventListenerCallback(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObj, size_t argumentCount, const JSValueRef* arguments, JSValueRef* exception) { assert(false); return JSValueMakeUndefined(ctx); }

    static JSValueRef ELEMENT_NODEConstGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) { assert(false); return JSValueMakeNumber(ctx, Arabica::DOM::Node_base::ELEMENT_NODE); }
    static JSValueRef ATTRIBUTE_NODEConstGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) { assert(false); return JSValueMakeNumber(ctx, Arabica::DOM::Node_base::ATTRIBUTE_NODE); }
    static JSValueRef TEXT_NODEConstGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) { assert(false); return JSValueMakeNumber(ctx, Arabica::DOM::Node_base::TEXT_NODE); }
    static JSValueRef CDATA_SECTION_NODEConstGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) { assert(false); return JSValueMakeNumber(ctx, Arabica::DOM::Node_base::CDATA_SECTION_NODE); }
    static JSValueRef ENTITY_REFERENCE_NODEConstGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) { assert(false); return JSValueMakeNumber(ctx, Arabica::DOM::Node_base::ENTITY_REFERENCE_NODE); }
    static JSValueRef ENTITY_NODEConstGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) { assert(false); return JSValueMakeNumber(ctx, Arabica::DOM::Node_base::ENTITY_NODE); }
    static JSValueRef PROCESSING_INSTRUCTION_NODEConstGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) { assert(false); return JSValueMakeNumber(ctx, Arabica::DOM::Node_base::PROCESSING_INSTRUCTION_NODE); }
    static JSValueRef COMMENT_NODEConstGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) { assert(false); return JSValueMakeNumber(ctx, Arabica::DOM::Node_base::COMMENT_NODE); }
    static JSValueRef DOCUMENT_NODEConstGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) { assert(false); return JSValueMakeNumber(ctx, Arabica::DOM::Node_base::DOCUMENT_NODE); }
    static JSValueRef DOCUMENT_TYPE_NODEConstGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) { assert(false); return JSValueMakeNumber(ctx, Arabica::DOM::Node_base::DOCUMENT_TYPE_NODE); }
    static JSValueRef DOCUMENT_FRAGMENT_NODEConstGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) { assert(false); return JSValueMakeNumber(ctx, Arabica::DOM::Node_base::DOCUMENT_FRAGMENT_NODE); }
    static JSValueRef NOTATION_NODEConstGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) { assert(false); return JSValueMakeNumber(ctx, Arabica::DOM::Node_base::NOTATION_NODE); }
    static JSValueRef MAX_TYPEConstGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) { assert(false); return JSValueMakeNumber(ctx, Arabica::DOM::Node_base::MAX_TYPE); }
    
	  JSC_DESTRUCTOR(Arabica::DOM::Node<std::string>);
    
    static JSStaticValue staticValues[];
    static JSStaticFunction staticFunctions[];

		static JSClassRef Tmpl;
		static JSClassRef getTmpl() {
		  if (Tmpl == NULL) {
        JSClassDefinition classDef = kJSClassDefinitionEmpty;
        classDef.staticValues = staticValues;
        classDef.staticFunctions = staticFunctions;
        classDef.finalize = jsDestructor;
        
		    Tmpl = JSClassCreate(&classDef);
        JSClassRetain(Tmpl);
      }
		  return Tmpl;
		}

	};

}


#endif /* end of include guard: JSCNODE_H_6BAK1S3C */
