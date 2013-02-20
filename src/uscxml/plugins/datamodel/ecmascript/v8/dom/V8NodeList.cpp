#include "V8Node.h"
#include "V8NodeList.h"

namespace Arabica {
namespace DOM {

  v8::Persistent<v8::FunctionTemplate> V8NodeList::Tmpl;


  v8::Handle<v8::Value> V8NodeList::lengthAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
    v8::Local<v8::Object> self = info.Holder();
    struct V8NodeListPrivate* privData = V8DOM::toClassPtr<V8NodeListPrivate >(self->GetInternalField(0));

    return v8::Integer::New(privData->nativeObj->getLength());
  }
  v8::Handle<v8::Value> V8NodeList::itemCallback(const v8::Arguments& args) {
    if (args.Length() < 1)
        throw V8Exception("Wrong number of arguments in item");

    v8::Local<v8::Object> self = args.Holder();
    struct V8NodeListPrivate* privData = V8DOM::toClassPtr<V8NodeListPrivate >(self->GetInternalField(0));
    unsigned long localIndex = args[0]->ToNumber()->Uint32Value();

    Arabica::DOM::Node<std::string>* retVal = new Arabica::DOM::Node<std::string>(privData->nativeObj->item(localIndex));
    v8::Handle<v8::Function> retCtor = V8Node::getTmpl()->GetFunction();
    v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

    struct V8Node::V8NodePrivate* retPrivData = new V8Node::V8NodePrivate();
    retPrivData->dom = privData->dom;
    retPrivData->nativeObj = retVal;

    retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));

    retObj.MakeWeak(0, V8Node::jsDestructor);
    return retObj;

  }

  bool V8NodeList::hasInstance(v8::Handle<v8::Value> value) {
    return getTmpl()->HasInstance(value);
  }

} 
} 
