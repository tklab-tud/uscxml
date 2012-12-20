#ifndef V8SCXMLDOM_H_AREM0ZC4
#define V8SCXMLDOM_H_AREM0ZC4

#include "uscxml/Interpreter.h"

#include <DOM/Document.hpp>
#include <v8.h>

#include <list>

namespace uscxml {

class V8SCXMLDOM {
public:
	V8SCXMLDOM();
	virtual ~V8SCXMLDOM() {};

	static v8::Handle<v8::ObjectTemplate> getDocument(Arabica::DOM::Document<std::string>& document);
	static v8::Handle<v8::Value> jsDocumentCreateElement(const v8::Arguments& args);
	static v8::Handle<v8::Value> jsDocumentEvaluate(const v8::Arguments& args);

	static v8::Handle<v8::Value> jsElementTagName(v8::Local<v8::String> property, const v8::AccessorInfo &info);
	static v8::Handle<v8::Value> jsElementGetAttribute(const v8::Arguments& args);
	static v8::Handle<v8::Value> jsElementSetAttribute(const v8::Arguments& args);
	static void jsElementDestructor(v8::Persistent<v8::Value> object, void* data);

	static v8::Handle<v8::Value> jsXPathValueAsNodeSet(const v8::Arguments& args);
	static void jsXPathValueDestructor(v8::Persistent<v8::Value> object, void* data);

	static v8::Handle<v8::Value> jsNodeSetGetIndex(uint32_t index, const v8::AccessorInfo &info);
	static v8::Handle<v8::Value> jsNodeSetLength(const v8::Arguments& args);
	static void jsNodeSetDestructor(v8::Persistent<v8::Value> object, void* data);

	static v8::Handle<v8::Value> jsNodeAppendChild(const v8::Arguments& args);
	static void jsNodeDestructor(v8::Persistent<v8::Value> object, void* data);

	static v8::Handle<v8::ObjectTemplate> getXPathValueTmpl();
	static v8::Handle<v8::ObjectTemplate> getNodeSetTmpl();
	static v8::Handle<v8::ObjectTemplate> getNodeTmpl();
	static v8::Handle<v8::ObjectTemplate> getElementTmpl();

	static v8::Handle<v8::ObjectTemplate> xPathValueTmpl;
	static v8::Handle<v8::ObjectTemplate> nodeSetTmpl;
	static v8::Handle<v8::ObjectTemplate> nodeTmpl;
	static v8::Handle<v8::ObjectTemplate> elementTmpl;

};

class V8Node {
};

class V8DOMDocument {
	V8DOMDocument();
	virtual ~V8DOMDocument();

	v8::Handle<v8::Array> jsChildNodes();
};

}

#endif /* end of include guard: V8SCXMLDOM_H_AREM0ZC4 */
