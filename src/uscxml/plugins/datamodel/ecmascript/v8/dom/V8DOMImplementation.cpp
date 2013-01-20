#include "V8DOMImplementation.h"
#include "V8Document.h"
#include "V8DocumentType.h"

namespace Arabica {
namespace DOM {

  v8::Persistent<v8::FunctionTemplate> V8DOMImplementation::Tmpl;

  v8::Handle<v8::Value> V8DOMImplementation::hasFeatureCallback(const v8::Arguments& args) {
    if (args.Length() < 2)
        throw V8Exception("Wrong number of arguments in hasFeature");

    v8::Local<v8::Object> self = args.Holder();
    V8DOMImplementationPrivate* privData = V8DOM::toClassPtr<V8DOMImplementationPrivate >(self->GetInternalField(0));
    v8::String::AsciiValue localFeature(args[0]);
    v8::String::AsciiValue localVersion(args[1]);

    bool retVal = privData->arabicaThis->hasFeature(*localFeature, *localVersion);

    return v8::Boolean::New(retVal);
  }

  v8::Handle<v8::Value> V8DOMImplementation::createDocumentTypeCallback(const v8::Arguments& args) {
    if (args.Length() < 3)
        throw V8Exception("Wrong number of arguments in createDocumentType");

    v8::Local<v8::Object> self = args.Holder();
    V8DOMImplementationPrivate* privData = V8DOM::toClassPtr<V8DOMImplementationPrivate >(self->GetInternalField(0));
    v8::String::AsciiValue localQualifiedName(args[0]);
    v8::String::AsciiValue localPublicId(args[1]);
    v8::String::AsciiValue localSystemId(args[2]);

    Arabica::DOM::DocumentType<std::string>* retVal = new Arabica::DOM::DocumentType<std::string>(privData->arabicaThis->createDocumentType(*localQualifiedName, *localPublicId, *localSystemId));
    v8::Handle<v8::Function> retCtor = V8DocumentType::getTmpl()->GetFunction();
    v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

    struct V8DocumentType::V8DocumentTypePrivate* retPrivData = new V8DocumentType::V8DocumentTypePrivate();
    retPrivData->dom = privData->dom;
    retPrivData->arabicaThis = retVal;

    retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));

    retObj.MakeWeak(0, V8DocumentType::jsDestructor);
    return retObj;

  }

  v8::Handle<v8::Value> V8DOMImplementation::createDocumentCallback(const v8::Arguments& args) {
    if (args.Length() < 3)
        throw V8Exception("Wrong number of arguments in createDocument");
    if (!(V8DocumentType::hasInstance(args[2])))
      throw V8Exception("Parameter mismatch while calling createDocument");

    v8::Local<v8::Object> self = args.Holder();
    V8DOMImplementationPrivate* privData = V8DOM::toClassPtr<V8DOMImplementationPrivate >(self->GetInternalField(0));
    v8::String::AsciiValue localNamespaceURI(args[0]);
    v8::String::AsciiValue localQualifiedName(args[1]);
    Arabica::DOM::DocumentType<std::string>* localDoctype = V8DOM::toClassPtr<V8DocumentType::V8DocumentTypePrivate >(args[2]->ToObject()->GetInternalField(0))->arabicaThis;

    Arabica::DOM::Document<std::string>* retVal = new Arabica::DOM::Document<std::string>(privData->arabicaThis->createDocument(*localNamespaceURI, *localQualifiedName, *localDoctype));
    v8::Handle<v8::Function> retCtor = V8Document::getTmpl()->GetFunction();
    v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

    struct V8Document::V8DocumentPrivate* retPrivData = new V8Document::V8DocumentPrivate();
    retPrivData->dom = privData->dom;
    retPrivData->arabicaThis = retVal;

    retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));

    retObj.MakeWeak(0, V8Document::jsDestructor);
    return retObj;

  }

  bool V8DOMImplementation::hasInstance(v8::Handle<v8::Value> value) {
    return getTmpl()->HasInstance(value);
  }

} 
} 
