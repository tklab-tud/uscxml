#include "V8DocumentType.h"
#include "V8NamedNodeMap.h"
#include "V8Node.h"

namespace Arabica {
namespace DOM {

v8::Persistent<v8::FunctionTemplate> V8DocumentType::Tmpl;


v8::Handle<v8::Value> V8DocumentType::nameAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8DocumentTypePrivate* privData = V8DOM::toClassPtr<V8DocumentTypePrivate >(self->GetInternalField(0));

	return v8::String::New(privData->arabicaThis->getName().c_str());
}

v8::Handle<v8::Value> V8DocumentType::entitiesAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8DocumentTypePrivate* privData = V8DOM::toClassPtr<V8DocumentTypePrivate >(self->GetInternalField(0));
	Arabica::DOM::NamedNodeMap<std::string>* arbaicaRet = new Arabica::DOM::NamedNodeMap<std::string>(privData->arabicaThis->getEntities());

	v8::Handle<v8::Function> arbaicaRetCtor = V8NamedNodeMap::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> arbaicaRetObj = v8::Persistent<v8::Object>::New(arbaicaRetCtor->NewInstance());

	struct V8NamedNodeMap::V8NamedNodeMapPrivate* retPrivData = new V8NamedNodeMap::V8NamedNodeMapPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->arabicaThis = arbaicaRet;

	arbaicaRetObj->SetInternalField(0, V8DOM::toExternal(retPrivData));
	arbaicaRetObj.MakeWeak(0, V8NamedNodeMap::jsDestructor);
	return arbaicaRetObj;

}

v8::Handle<v8::Value> V8DocumentType::notationsAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8DocumentTypePrivate* privData = V8DOM::toClassPtr<V8DocumentTypePrivate >(self->GetInternalField(0));
	Arabica::DOM::NamedNodeMap<std::string>* arbaicaRet = new Arabica::DOM::NamedNodeMap<std::string>(privData->arabicaThis->getNotations());

	v8::Handle<v8::Function> arbaicaRetCtor = V8NamedNodeMap::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> arbaicaRetObj = v8::Persistent<v8::Object>::New(arbaicaRetCtor->NewInstance());

	struct V8NamedNodeMap::V8NamedNodeMapPrivate* retPrivData = new V8NamedNodeMap::V8NamedNodeMapPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->arabicaThis = arbaicaRet;

	arbaicaRetObj->SetInternalField(0, V8DOM::toExternal(retPrivData));
	arbaicaRetObj.MakeWeak(0, V8NamedNodeMap::jsDestructor);
	return arbaicaRetObj;

}

v8::Handle<v8::Value> V8DocumentType::publicIdAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8DocumentTypePrivate* privData = V8DOM::toClassPtr<V8DocumentTypePrivate >(self->GetInternalField(0));

	return v8::String::New(privData->arabicaThis->getPublicId().c_str());
}

v8::Handle<v8::Value> V8DocumentType::systemIdAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8DocumentTypePrivate* privData = V8DOM::toClassPtr<V8DocumentTypePrivate >(self->GetInternalField(0));

	return v8::String::New(privData->arabicaThis->getSystemId().c_str());
}

v8::Handle<v8::Value> V8DocumentType::internalSubsetAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8DocumentTypePrivate* privData = V8DOM::toClassPtr<V8DocumentTypePrivate >(self->GetInternalField(0));

	return v8::String::New(privData->arabicaThis->getInternalSubset().c_str());
}
bool V8DocumentType::hasInstance(v8::Handle<v8::Value> value) {
	return getTmpl()->HasInstance(value);
}

}
}
