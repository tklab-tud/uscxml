#include "JSCDOMImplementation.h"
#include "JSCDocument.h"
#include "JSCDocumentType.h"
#include "JSCElement.h"
#include "JSCNode.h"

namespace Arabica {
namespace DOM {


JSStaticValue JSCDocument::staticValues[] = {
	{ "doctype", doctypeAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "implementation", implementationAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },
	{ "documentElement", documentElementAttrGetter, 0, kJSPropertyAttributeDontDelete | kJSPropertyAttributeReadOnly },

	{ 0, 0, 0, 0 }
};

JSStaticFunction JSCDocument::staticFunctions[] = {
	{ "createElement", createElementCallback, kJSPropertyAttributeDontDelete },
	{ "createDocumentFragment", createDocumentFragmentCallback, kJSPropertyAttributeDontDelete },
	{ "createTextNode", createTextNodeCallback, kJSPropertyAttributeDontDelete },
	{ "createComment", createCommentCallback, kJSPropertyAttributeDontDelete },
	{ "createCDATASection", createCDATASectionCallback, kJSPropertyAttributeDontDelete },
	{ "createProcessingInstruction", createProcessingInstructionCallback, kJSPropertyAttributeDontDelete },
	{ "createAttribute", createAttributeCallback, kJSPropertyAttributeDontDelete },
	{ "createEntityReference", createEntityReferenceCallback, kJSPropertyAttributeDontDelete },
	{ "getElementsByTagName", getElementsByTagNameCallback, kJSPropertyAttributeDontDelete },
	{ "importNode", importNodeCallback, kJSPropertyAttributeDontDelete },
	{ "createElementNS", createElementNSCallback, kJSPropertyAttributeDontDelete },
	{ "createAttributeNS", createAttributeNSCallback, kJSPropertyAttributeDontDelete },
	{ "getElementsByTagNameNS", getElementsByTagNameNSCallback, kJSPropertyAttributeDontDelete },
	{ "getElementById", getElementByIdCallback, kJSPropertyAttributeDontDelete },
	{ "evaluate", evaluateCustomCallback, kJSPropertyAttributeDontDelete },
	{ 0, 0, 0 }
};

JSValueRef JSCDocument::doctypeAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCDocumentPrivate* privData = static_cast<JSCDocument::JSCDocumentPrivate* >(JSObjectGetPrivate(thisObj));
	Arabica::DOM::DocumentType<std::string>* arbaicaRet = new Arabica::DOM::DocumentType<std::string>(privData->arabicaThis->getDoctype());

	struct JSCDocumentType::JSCDocumentTypePrivate* retPrivData = new JSCDocumentType::JSCDocumentTypePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->arabicaThis = arbaicaRet;

	JSObjectRef arbaicaRetObj = JSObjectMake(ctx, JSCDocumentType::getTmpl(), retPrivData);
	return arbaicaRetObj;

}

JSValueRef JSCDocument::implementationAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCDocumentPrivate* privData = static_cast<JSCDocument::JSCDocumentPrivate* >(JSObjectGetPrivate(thisObj));
	Arabica::DOM::DOMImplementation<std::string>* arbaicaRet = new Arabica::DOM::DOMImplementation<std::string>(privData->arabicaThis->getImplementation());

	struct JSCDOMImplementation::JSCDOMImplementationPrivate* retPrivData = new JSCDOMImplementation::JSCDOMImplementationPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->arabicaThis = arbaicaRet;

	JSObjectRef arbaicaRetObj = JSObjectMake(ctx, JSCDOMImplementation::getTmpl(), retPrivData);
	return arbaicaRetObj;

}

JSValueRef JSCDocument::documentElementAttrGetter(JSContextRef ctx, JSObjectRef thisObj, JSStringRef propertyName, JSValueRef* exception) {
	struct JSCDocumentPrivate* privData = static_cast<JSCDocument::JSCDocumentPrivate* >(JSObjectGetPrivate(thisObj));
	Arabica::DOM::Element<std::string>* arbaicaRet = new Arabica::DOM::Element<std::string>(privData->arabicaThis->getDocumentElement());

	struct JSCElement::JSCElementPrivate* retPrivData = new JSCElement::JSCElementPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->arabicaThis = arbaicaRet;

	JSObjectRef arbaicaRetObj = JSObjectMake(ctx, JSCElement::getTmpl(), retPrivData);
	return arbaicaRetObj;

}

}
}
