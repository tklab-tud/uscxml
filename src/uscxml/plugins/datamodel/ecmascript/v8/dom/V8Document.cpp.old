#include "V8Document.h"
#include "V8Element.h"
#include "V8XPathResult.h"

namespace uscxml {

using namespace Arabica::DOM;
using namespace Arabica::XPath;

v8::Persistent<v8::FunctionTemplate> V8Document::Tmpl;

v8::Handle<v8::Value> V8Document::createElementCallback(const v8::Arguments& args) {
  ASSERT_ARGS1(args, IsString);
  v8::String::AsciiValue tagName(args[0]);
  
  v8::Local<v8::Object> self = args.Holder();
  Document<std::string>* doc = V8DOM::toClassPtr<Document<std::string> >(self->GetInternalField(0));
  V8DOM* dom = V8DOM::toClassPtr<V8DOM>(self->GetInternalField(1)); (void)dom;
  
  Element<std::string>* element = new Element<std::string>(doc->createElement(*tagName));
  
  v8::Handle<v8::Function> elemCtor = V8Element::getTmpl()->GetFunction();
  v8::Persistent<v8::Object> elemObj = v8::Persistent<v8::Object>::New(elemCtor->NewInstance());
  
  elemObj->SetInternalField(0, V8DOM::toExternal(element));
  elemObj->SetInternalField(1, self->GetInternalField(1));
  
  elemObj.MakeWeak(0, V8Element::jsDestructor);
  return elemObj;
}
  
v8::Handle<v8::Value> V8Document::evaluateCallback(const v8::Arguments& args) {
  ASSERT_ARGS1(args, IsString);
  v8::String::AsciiValue xpathExpr(args[0]);

  v8::Local<v8::Object> self = args.Holder();
  Document<std::string>* doc = V8DOM::toClassPtr<Document<std::string> >(self->GetInternalField(0));
  V8DOM* dom = V8DOM::toClassPtr<V8DOM>(self->GetInternalField(1)); (void)dom;

  Node<std::string>* context;
	if (args.Length() > 1) {
		context = V8DOM::toClassPtr<Node<std::string> >(args[1]->ToObject()->GetInternalField(0));
	} else {
		context = doc;
	}

	XPathValue<std::string>* xpathValue = new XPathValue<std::string>(dom->xpath->evaluate(*xpathExpr, *context));
  
  v8::Handle<v8::Function> xpathResultCtor = V8XPathResult::getTmpl()->GetFunction();
  v8::Persistent<v8::Object> xpathResultObj = v8::Persistent<v8::Object>::New(xpathResultCtor->NewInstance());
  
  xpathResultObj->SetInternalField(0, V8DOM::toExternal(xpathValue));
  xpathResultObj->SetInternalField(1, self->GetInternalField(1));
  
  xpathResultObj.MakeWeak(0, V8XPathResult::jsDestructor);
  return xpathResultObj;
}

}