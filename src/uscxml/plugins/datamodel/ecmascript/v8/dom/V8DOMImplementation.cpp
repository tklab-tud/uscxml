#include "V8DOMImplementation.h"
#include "V8Document.h"
#include "V8DocumentType.h"

namespace Arabica {
namespace DOM {

v8::Persistent<v8::FunctionTemplate> V8DOMImplementation::Tmpl;

v8::Handle<v8::Value> V8DOMImplementation::hasFeatureCallback(const v8::Arguments& args) {

	v8::Local<v8::Object> self = args.Holder();
	struct V8DOMImplementationPrivate* privData = V8DOM::toClassPtr<V8DOMImplementationPrivate >(self->GetInternalField(0));
	if (false) {
	} else if (args.Length() == 2 &&
	           args[0]->IsString() &&
	           args[1]->IsString()) {
		v8::String::AsciiValue localFeature(args[0]);
		v8::String::AsciiValue localVersion(args[1]);

		bool retVal = privData->nativeObj->hasFeature(*localFeature, *localVersion);

		return v8::Boolean::New(retVal);
	}
	throw V8Exception("Parameter mismatch while calling hasFeature");
	return v8::Undefined();
}

v8::Handle<v8::Value> V8DOMImplementation::createDocumentTypeCallback(const v8::Arguments& args) {

	v8::Local<v8::Object> self = args.Holder();
	struct V8DOMImplementationPrivate* privData = V8DOM::toClassPtr<V8DOMImplementationPrivate >(self->GetInternalField(0));
	if (false) {
	} else if (args.Length() == 3 &&
	           args[0]->IsString() &&
	           args[1]->IsString() &&
	           args[2]->IsString()) {
		v8::String::AsciiValue localQualifiedName(args[0]);
		v8::String::AsciiValue localPublicId(args[1]);
		v8::String::AsciiValue localSystemId(args[2]);

		Arabica::DOM::DocumentType<std::string>* retVal = new Arabica::DOM::DocumentType<std::string>(privData->nativeObj->createDocumentType(*localQualifiedName, *localPublicId, *localSystemId));
		v8::Handle<v8::Function> retCtor = V8DocumentType::getTmpl()->GetFunction();
		v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

		struct V8DocumentType::V8DocumentTypePrivate* retPrivData = new V8DocumentType::V8DocumentTypePrivate();
		retPrivData->dom = privData->dom;
		retPrivData->nativeObj = retVal;

		retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));

		retObj.MakeWeak(0, V8DocumentType::jsDestructor);
		return retObj;

	}
	throw V8Exception("Parameter mismatch while calling createDocumentType");
	return v8::Undefined();
}

v8::Handle<v8::Value> V8DOMImplementation::createDocumentCallback(const v8::Arguments& args) {

	v8::Local<v8::Object> self = args.Holder();
	struct V8DOMImplementationPrivate* privData = V8DOM::toClassPtr<V8DOMImplementationPrivate >(self->GetInternalField(0));
	if (false) {
	} else if (args.Length() == 3 &&
	           args[0]->IsString() &&
	           args[1]->IsString() &&
	           args[2]->IsObject() && V8DocumentType::hasInstance(args[2])) {
		v8::String::AsciiValue localNamespaceURI(args[0]);
		v8::String::AsciiValue localQualifiedName(args[1]);
		Arabica::DOM::DocumentType<std::string>* localDoctype = V8DOM::toClassPtr<V8DocumentType::V8DocumentTypePrivate >(args[2]->ToObject()->GetInternalField(0))->nativeObj;

		Arabica::DOM::Document<std::string>* retVal = new Arabica::DOM::Document<std::string>(privData->nativeObj->createDocument(*localNamespaceURI, *localQualifiedName, *localDoctype));
		v8::Handle<v8::Function> retCtor = V8Document::getTmpl()->GetFunction();
		v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

		struct V8Document::V8DocumentPrivate* retPrivData = new V8Document::V8DocumentPrivate();
		retPrivData->dom = privData->dom;
		retPrivData->nativeObj = retVal;

		retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));

		retObj.MakeWeak(0, V8Document::jsDestructor);
		return retObj;

	}
	throw V8Exception("Parameter mismatch while calling createDocument");
	return v8::Undefined();
}
bool V8DOMImplementation::hasInstance(v8::Handle<v8::Value> value) {
	return getTmpl()->HasInstance(value);
}

}
}
