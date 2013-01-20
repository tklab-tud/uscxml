#include "JSCNode.h"
#include <DOM/Node.hpp>

namespace uscxml {

using namespace Arabica::DOM;

  JSStaticValue JSCNode::staticValues[] = {
    { "nodeName", nodeNameAttrGetter, nodeValueAttrSetter, kJSPropertyAttributeDontDelete },
    { "nodeValue", nodeValueAttrGetter, NULL, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
    { "nodeType", nodeValueAttrGetter, NULL, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
    { "parentNode", nodeValueAttrGetter, NULL, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
    { "childNodes", nodeValueAttrGetter, NULL, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
    { "firstChild", nodeValueAttrGetter, NULL, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
    { "lastChild", nodeValueAttrGetter, NULL, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
    { "previousSibling", nodeValueAttrGetter, NULL, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
    { "nextSibling", nodeValueAttrGetter, NULL, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
    { "attributes", nodeValueAttrGetter, NULL, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
    { "ownerDocument", nodeValueAttrGetter, NULL, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
    { "namespaceURI", nodeValueAttrGetter, NULL, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
    { "prefix", nodeValueAttrGetter, prefixAttrSetter, kJSPropertyAttributeDontDelete },
    { "localName", nodeValueAttrGetter, NULL, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
    { "baseURI", nodeValueAttrGetter, NULL, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
    { "textContent", nodeValueAttrGetter, textContentAttrSetter, kJSPropertyAttributeDontDelete },
    { "parentElement", nodeValueAttrGetter, NULL, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
    { "ELEMENT_NODE", ELEMENT_NODEConstGetter, NULL, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
    { "ATTRIBUTE_NODE", ATTRIBUTE_NODEConstGetter, NULL, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
    { "TEXT_NODE", TEXT_NODEConstGetter, NULL, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
    { "CDATA_SECTION_NODE", CDATA_SECTION_NODEConstGetter, NULL, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
    { "ENTITY_REFERENCE_NODE", ENTITY_REFERENCE_NODEConstGetter, NULL, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
    { "ENTITY_NODE", ENTITY_NODEConstGetter, NULL, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
    { "PROCESSING_INSTRUCTION_NODE", PROCESSING_INSTRUCTION_NODEConstGetter, NULL, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
    { "COMMENT_NODE", COMMENT_NODEConstGetter, NULL, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
    { "DOCUMENT_NODE", DOCUMENT_NODEConstGetter, NULL, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
    { "DOCUMENT_TYPE_NODE", DOCUMENT_TYPE_NODEConstGetter, NULL, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
    { "DOCUMENT_FRAGMENT_NODE", DOCUMENT_FRAGMENT_NODEConstGetter, NULL, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
    { "NOTATION_NODE", NOTATION_NODEConstGetter, NULL, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
    { "MAX_TYPE", MAX_TYPEConstGetter, NULL, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
    { 0, 0, 0, 0 }
  };  

  JSStaticFunction JSCNode::staticFunctions[] = {
    { "insertBefore", insertBeforeCallback, kJSPropertyAttributeDontDelete },
    { "replaceChild", replaceChildCallback, kJSPropertyAttributeDontDelete },
    { "removeChild", removeChildCallback, kJSPropertyAttributeDontDelete },
    { "appendChild", appendChildCallback, kJSPropertyAttributeDontDelete },
    { "hasChildNodes", hasChildNodesCallback, kJSPropertyAttributeDontDelete },
    { "cloneNode", cloneNodeCallback, kJSPropertyAttributeDontDelete },
    { "normalize", normalizeCallback, kJSPropertyAttributeDontDelete },
    { "isSupported", isSupportedCallback, kJSPropertyAttributeDontDelete },
    { "hasAttributes", hasAttributesCallback, kJSPropertyAttributeDontDelete },
    { "lookupPrefix", lookupPrefixCallback, kJSPropertyAttributeDontDelete },
    { "isDefaultNamespace", isDefaultNamespaceCallback, kJSPropertyAttributeDontDelete },
    { "lookupNamespaceURI", lookupNamespaceURICallback, kJSPropertyAttributeDontDelete },
    { "addEventListener", addEventListenerCallback, kJSPropertyAttributeDontDelete },
    { "removeEventListener", removeEventListenerCallback, kJSPropertyAttributeDontDelete },
    { 0, 0, 0 }
  };
  
}