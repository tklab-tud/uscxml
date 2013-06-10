#include "V8Attr.h"
#include "V8Element.h"
#include "V8Node.h"
#include "V8NodeList.h"

namespace Arabica {
namespace DOM {

  v8::Persistent<v8::FunctionTemplate> V8Element::Tmpl;


  v8::Handle<v8::Value> V8Element::tagNameAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
    v8::Local<v8::Object> self = info.Holder();
    struct V8ElementPrivate* privData = V8DOM::toClassPtr<V8ElementPrivate >(self->GetInternalField(0));

    return v8::String::New(privData->nativeObj->getTagName().c_str());
  }
  v8::Handle<v8::Value> V8Element::getAttributeCallback(const v8::Arguments& args) {
    if (args.Length() < 1)
        throw V8Exception("Wrong number of arguments in getAttribute");

    v8::Local<v8::Object> self = args.Holder();
    struct V8ElementPrivate* privData = V8DOM::toClassPtr<V8ElementPrivate >(self->GetInternalField(0));
    v8::String::AsciiValue localName(args[0]);

    std::string retVal = privData->nativeObj->getAttribute(*localName);

    return v8::String::New(retVal.c_str());
  }

  v8::Handle<v8::Value> V8Element::setAttributeCallback(const v8::Arguments& args) {
    if (args.Length() < 2)
        throw V8Exception("Wrong number of arguments in setAttribute");

    v8::Local<v8::Object> self = args.Holder();
    struct V8ElementPrivate* privData = V8DOM::toClassPtr<V8ElementPrivate >(self->GetInternalField(0));
    v8::String::AsciiValue localName(args[0]);
    v8::String::AsciiValue localValue(args[1]);

    privData->nativeObj->setAttribute(*localName, *localValue);

    return v8::Undefined();
  }

  v8::Handle<v8::Value> V8Element::removeAttributeCallback(const v8::Arguments& args) {
    if (args.Length() < 1)
        throw V8Exception("Wrong number of arguments in removeAttribute");

    v8::Local<v8::Object> self = args.Holder();
    struct V8ElementPrivate* privData = V8DOM::toClassPtr<V8ElementPrivate >(self->GetInternalField(0));
    v8::String::AsciiValue localName(args[0]);

    privData->nativeObj->removeAttribute(*localName);

    return v8::Undefined();
  }

  v8::Handle<v8::Value> V8Element::getAttributeNodeCallback(const v8::Arguments& args) {
    if (args.Length() < 1)
        throw V8Exception("Wrong number of arguments in getAttributeNode");

    v8::Local<v8::Object> self = args.Holder();
    struct V8ElementPrivate* privData = V8DOM::toClassPtr<V8ElementPrivate >(self->GetInternalField(0));
    v8::String::AsciiValue localName(args[0]);

    Arabica::DOM::Attr<std::string>* retVal = new Arabica::DOM::Attr<std::string>(privData->nativeObj->getAttributeNode(*localName));
    v8::Handle<v8::Function> retCtor = V8Attr::getTmpl()->GetFunction();
    v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

    struct V8Attr::V8AttrPrivate* retPrivData = new V8Attr::V8AttrPrivate();
    retPrivData->dom = privData->dom;
    retPrivData->nativeObj = retVal;

    retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));

    retObj.MakeWeak(0, V8Attr::jsDestructor);
    return retObj;

  }

  v8::Handle<v8::Value> V8Element::setAttributeNodeCallback(const v8::Arguments& args) {
    if (args.Length() < 1)
        throw V8Exception("Wrong number of arguments in setAttributeNode");
    if (!(V8Attr::hasInstance(args[0])))
      throw V8Exception("Parameter mismatch while calling setAttributeNode");

    v8::Local<v8::Object> self = args.Holder();
    struct V8ElementPrivate* privData = V8DOM::toClassPtr<V8ElementPrivate >(self->GetInternalField(0));
    Arabica::DOM::Attr<std::string>* localNewAttr = V8DOM::toClassPtr<V8Attr::V8AttrPrivate >(args[0]->ToObject()->GetInternalField(0))->nativeObj;

    Arabica::DOM::Attr<std::string>* retVal = new Arabica::DOM::Attr<std::string>(privData->nativeObj->setAttributeNode(*localNewAttr));
    v8::Handle<v8::Function> retCtor = V8Attr::getTmpl()->GetFunction();
    v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

    struct V8Attr::V8AttrPrivate* retPrivData = new V8Attr::V8AttrPrivate();
    retPrivData->dom = privData->dom;
    retPrivData->nativeObj = retVal;

    retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));

    retObj.MakeWeak(0, V8Attr::jsDestructor);
    return retObj;

  }

  v8::Handle<v8::Value> V8Element::removeAttributeNodeCallback(const v8::Arguments& args) {
    if (args.Length() < 1)
        throw V8Exception("Wrong number of arguments in removeAttributeNode");
    if (!(V8Attr::hasInstance(args[0])))
      throw V8Exception("Parameter mismatch while calling removeAttributeNode");

    v8::Local<v8::Object> self = args.Holder();
    struct V8ElementPrivate* privData = V8DOM::toClassPtr<V8ElementPrivate >(self->GetInternalField(0));
    Arabica::DOM::Attr<std::string>* localOldAttr = V8DOM::toClassPtr<V8Attr::V8AttrPrivate >(args[0]->ToObject()->GetInternalField(0))->nativeObj;

    Arabica::DOM::Attr<std::string>* retVal = new Arabica::DOM::Attr<std::string>(privData->nativeObj->removeAttributeNode(*localOldAttr));
    v8::Handle<v8::Function> retCtor = V8Attr::getTmpl()->GetFunction();
    v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

    struct V8Attr::V8AttrPrivate* retPrivData = new V8Attr::V8AttrPrivate();
    retPrivData->dom = privData->dom;
    retPrivData->nativeObj = retVal;

    retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));

    retObj.MakeWeak(0, V8Attr::jsDestructor);
    return retObj;

  }

  v8::Handle<v8::Value> V8Element::getElementsByTagNameCallback(const v8::Arguments& args) {
    if (args.Length() < 1)
        throw V8Exception("Wrong number of arguments in getElementsByTagName");

    v8::Local<v8::Object> self = args.Holder();
    struct V8ElementPrivate* privData = V8DOM::toClassPtr<V8ElementPrivate >(self->GetInternalField(0));
    v8::String::AsciiValue localName(args[0]);

    Arabica::DOM::NodeList<std::string>* retVal = new Arabica::DOM::NodeList<std::string>(privData->nativeObj->getElementsByTagName(*localName));
    v8::Handle<v8::Function> retCtor = V8NodeList::getTmpl()->GetFunction();
    v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

    struct V8NodeList::V8NodeListPrivate* retPrivData = new V8NodeList::V8NodeListPrivate();
    retPrivData->dom = privData->dom;
    retPrivData->nativeObj = retVal;

    retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));

    retObj.MakeWeak(0, V8NodeList::jsDestructor);
    return retObj;

  }

  v8::Handle<v8::Value> V8Element::getAttributeNSCallback(const v8::Arguments& args) {
    if (args.Length() < 2)
        throw V8Exception("Wrong number of arguments in getAttributeNS");

    v8::Local<v8::Object> self = args.Holder();
    struct V8ElementPrivate* privData = V8DOM::toClassPtr<V8ElementPrivate >(self->GetInternalField(0));
    v8::String::AsciiValue localNamespaceURI(args[0]);
    v8::String::AsciiValue localLocalName(args[1]);

    std::string retVal = privData->nativeObj->getAttributeNS(*localNamespaceURI, *localLocalName);

    return v8::String::New(retVal.c_str());
  }

  v8::Handle<v8::Value> V8Element::setAttributeNSCallback(const v8::Arguments& args) {
    if (args.Length() < 3)
        throw V8Exception("Wrong number of arguments in setAttributeNS");

    v8::Local<v8::Object> self = args.Holder();
    struct V8ElementPrivate* privData = V8DOM::toClassPtr<V8ElementPrivate >(self->GetInternalField(0));
    v8::String::AsciiValue localNamespaceURI(args[0]);
    v8::String::AsciiValue localQualifiedName(args[1]);
    v8::String::AsciiValue localValue(args[2]);

    privData->nativeObj->setAttributeNS(*localNamespaceURI, *localQualifiedName, *localValue);

    return v8::Undefined();
  }

  v8::Handle<v8::Value> V8Element::removeAttributeNSCallback(const v8::Arguments& args) {
    if (args.Length() < 2)
        throw V8Exception("Wrong number of arguments in removeAttributeNS");

    v8::Local<v8::Object> self = args.Holder();
    struct V8ElementPrivate* privData = V8DOM::toClassPtr<V8ElementPrivate >(self->GetInternalField(0));
    v8::String::AsciiValue localNamespaceURI(args[0]);
    v8::String::AsciiValue localLocalName(args[1]);

    privData->nativeObj->removeAttributeNS(*localNamespaceURI, *localLocalName);

    return v8::Undefined();
  }

  v8::Handle<v8::Value> V8Element::getAttributeNodeNSCallback(const v8::Arguments& args) {
    if (args.Length() < 2)
        throw V8Exception("Wrong number of arguments in getAttributeNodeNS");

    v8::Local<v8::Object> self = args.Holder();
    struct V8ElementPrivate* privData = V8DOM::toClassPtr<V8ElementPrivate >(self->GetInternalField(0));
    v8::String::AsciiValue localNamespaceURI(args[0]);
    v8::String::AsciiValue localLocalName(args[1]);

    Arabica::DOM::Attr<std::string>* retVal = new Arabica::DOM::Attr<std::string>(privData->nativeObj->getAttributeNodeNS(*localNamespaceURI, *localLocalName));
    v8::Handle<v8::Function> retCtor = V8Attr::getTmpl()->GetFunction();
    v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

    struct V8Attr::V8AttrPrivate* retPrivData = new V8Attr::V8AttrPrivate();
    retPrivData->dom = privData->dom;
    retPrivData->nativeObj = retVal;

    retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));

    retObj.MakeWeak(0, V8Attr::jsDestructor);
    return retObj;

  }

  v8::Handle<v8::Value> V8Element::setAttributeNodeNSCallback(const v8::Arguments& args) {
    if (args.Length() < 1)
        throw V8Exception("Wrong number of arguments in setAttributeNodeNS");
    if (!(V8Attr::hasInstance(args[0])))
      throw V8Exception("Parameter mismatch while calling setAttributeNodeNS");

    v8::Local<v8::Object> self = args.Holder();
    struct V8ElementPrivate* privData = V8DOM::toClassPtr<V8ElementPrivate >(self->GetInternalField(0));
    Arabica::DOM::Attr<std::string>* localNewAttr = V8DOM::toClassPtr<V8Attr::V8AttrPrivate >(args[0]->ToObject()->GetInternalField(0))->nativeObj;

    Arabica::DOM::Attr<std::string>* retVal = new Arabica::DOM::Attr<std::string>(privData->nativeObj->setAttributeNodeNS(*localNewAttr));
    v8::Handle<v8::Function> retCtor = V8Attr::getTmpl()->GetFunction();
    v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

    struct V8Attr::V8AttrPrivate* retPrivData = new V8Attr::V8AttrPrivate();
    retPrivData->dom = privData->dom;
    retPrivData->nativeObj = retVal;

    retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));

    retObj.MakeWeak(0, V8Attr::jsDestructor);
    return retObj;

  }

  v8::Handle<v8::Value> V8Element::getElementsByTagNameNSCallback(const v8::Arguments& args) {
    if (args.Length() < 2)
        throw V8Exception("Wrong number of arguments in getElementsByTagNameNS");

    v8::Local<v8::Object> self = args.Holder();
    struct V8ElementPrivate* privData = V8DOM::toClassPtr<V8ElementPrivate >(self->GetInternalField(0));
    v8::String::AsciiValue localNamespaceURI(args[0]);
    v8::String::AsciiValue localLocalName(args[1]);

    Arabica::DOM::NodeList<std::string>* retVal = new Arabica::DOM::NodeList<std::string>(privData->nativeObj->getElementsByTagNameNS(*localNamespaceURI, *localLocalName));
    v8::Handle<v8::Function> retCtor = V8NodeList::getTmpl()->GetFunction();
    v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

    struct V8NodeList::V8NodeListPrivate* retPrivData = new V8NodeList::V8NodeListPrivate();
    retPrivData->dom = privData->dom;
    retPrivData->nativeObj = retVal;

    retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));

    retObj.MakeWeak(0, V8NodeList::jsDestructor);
    return retObj;

  }

  v8::Handle<v8::Value> V8Element::hasAttributeCallback(const v8::Arguments& args) {
    if (args.Length() < 1)
        throw V8Exception("Wrong number of arguments in hasAttribute");

    v8::Local<v8::Object> self = args.Holder();
    struct V8ElementPrivate* privData = V8DOM::toClassPtr<V8ElementPrivate >(self->GetInternalField(0));
    v8::String::AsciiValue localName(args[0]);

    bool retVal = privData->nativeObj->hasAttribute(*localName);

    return v8::Boolean::New(retVal);
  }

  v8::Handle<v8::Value> V8Element::hasAttributeNSCallback(const v8::Arguments& args) {
    if (args.Length() < 2)
        throw V8Exception("Wrong number of arguments in hasAttributeNS");

    v8::Local<v8::Object> self = args.Holder();
    struct V8ElementPrivate* privData = V8DOM::toClassPtr<V8ElementPrivate >(self->GetInternalField(0));
    v8::String::AsciiValue localNamespaceURI(args[0]);
    v8::String::AsciiValue localLocalName(args[1]);

    bool retVal = privData->nativeObj->hasAttributeNS(*localNamespaceURI, *localLocalName);

    return v8::Boolean::New(retVal);
  }

  bool V8Element::hasInstance(v8::Handle<v8::Value> value) {
    return getTmpl()->HasInstance(value);
  }

} 
} 
