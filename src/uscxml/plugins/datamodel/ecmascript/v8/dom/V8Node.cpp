#include "V8Document.h"
#include "V8NamedNodeMap.h"
#include "V8Node.h"
#include "V8NodeList.h"

namespace Arabica {
namespace DOM {

v8::Persistent<v8::FunctionTemplate> V8Node::Tmpl;


v8::Handle<v8::Value> V8Node::nodeNameAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8NodePrivate* privData = V8DOM::toClassPtr<V8NodePrivate >(self->GetInternalField(0));

	return v8::String::New(privData->nativeObj->getNodeName().c_str());
}

v8::Handle<v8::Value> V8Node::nodeValueAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8NodePrivate* privData = V8DOM::toClassPtr<V8NodePrivate >(self->GetInternalField(0));

	return v8::String::New(privData->nativeObj->getNodeValue().c_str());
}

void V8Node::nodeValueAttrSetter(v8::Local<v8::String> property, v8::Local<v8::Value> value, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8NodePrivate* privData = V8DOM::toClassPtr<V8NodePrivate >(self->GetInternalField(0));
	v8::String::AsciiValue localNodeValue(value);
	privData->nativeObj->setNodeValue(*localNodeValue);
}

v8::Handle<v8::Value> V8Node::nodeTypeAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8NodePrivate* privData = V8DOM::toClassPtr<V8NodePrivate >(self->GetInternalField(0));

	return v8::Integer::New(privData->nativeObj->getNodeType());
}

v8::Handle<v8::Value> V8Node::parentNodeAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8NodePrivate* privData = V8DOM::toClassPtr<V8NodePrivate >(self->GetInternalField(0));

	if (!privData->nativeObj->getParentNode()) return v8::Undefined();
	Arabica::DOM::Node<std::string>* arbaicaRet = new Arabica::DOM::Node<std::string>(privData->nativeObj->getParentNode());

	v8::Handle<v8::Function> arbaicaRetCtor = V8Node::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> arbaicaRetObj = v8::Persistent<v8::Object>::New(arbaicaRetCtor->NewInstance());

	struct V8Node::V8NodePrivate* retPrivData = new V8Node::V8NodePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = arbaicaRet;

	arbaicaRetObj->SetInternalField(0, V8DOM::toExternal(retPrivData));
	arbaicaRetObj.MakeWeak(0, V8Node::jsDestructor);
	return arbaicaRetObj;

}

v8::Handle<v8::Value> V8Node::childNodesAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8NodePrivate* privData = V8DOM::toClassPtr<V8NodePrivate >(self->GetInternalField(0));


	Arabica::DOM::NodeList<std::string>* arbaicaRet = new Arabica::DOM::NodeList<std::string>(privData->nativeObj->getChildNodes());

	v8::Handle<v8::Function> arbaicaRetCtor = V8NodeList::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> arbaicaRetObj = v8::Persistent<v8::Object>::New(arbaicaRetCtor->NewInstance());

	struct V8NodeList::V8NodeListPrivate* retPrivData = new V8NodeList::V8NodeListPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = arbaicaRet;

	arbaicaRetObj->SetInternalField(0, V8DOM::toExternal(retPrivData));
	arbaicaRetObj.MakeWeak(0, V8NodeList::jsDestructor);
	return arbaicaRetObj;

}

v8::Handle<v8::Value> V8Node::firstChildAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8NodePrivate* privData = V8DOM::toClassPtr<V8NodePrivate >(self->GetInternalField(0));

	if (!privData->nativeObj->getFirstChild()) return v8::Undefined();
	Arabica::DOM::Node<std::string>* arbaicaRet = new Arabica::DOM::Node<std::string>(privData->nativeObj->getFirstChild());

	v8::Handle<v8::Function> arbaicaRetCtor = V8Node::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> arbaicaRetObj = v8::Persistent<v8::Object>::New(arbaicaRetCtor->NewInstance());

	struct V8Node::V8NodePrivate* retPrivData = new V8Node::V8NodePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = arbaicaRet;

	arbaicaRetObj->SetInternalField(0, V8DOM::toExternal(retPrivData));
	arbaicaRetObj.MakeWeak(0, V8Node::jsDestructor);
	return arbaicaRetObj;

}

v8::Handle<v8::Value> V8Node::lastChildAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8NodePrivate* privData = V8DOM::toClassPtr<V8NodePrivate >(self->GetInternalField(0));

	if (!privData->nativeObj->getLastChild()) return v8::Undefined();
	Arabica::DOM::Node<std::string>* arbaicaRet = new Arabica::DOM::Node<std::string>(privData->nativeObj->getLastChild());

	v8::Handle<v8::Function> arbaicaRetCtor = V8Node::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> arbaicaRetObj = v8::Persistent<v8::Object>::New(arbaicaRetCtor->NewInstance());

	struct V8Node::V8NodePrivate* retPrivData = new V8Node::V8NodePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = arbaicaRet;

	arbaicaRetObj->SetInternalField(0, V8DOM::toExternal(retPrivData));
	arbaicaRetObj.MakeWeak(0, V8Node::jsDestructor);
	return arbaicaRetObj;

}

v8::Handle<v8::Value> V8Node::previousSiblingAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8NodePrivate* privData = V8DOM::toClassPtr<V8NodePrivate >(self->GetInternalField(0));

	if (!privData->nativeObj->getPreviousSibling()) return v8::Undefined();
	Arabica::DOM::Node<std::string>* arbaicaRet = new Arabica::DOM::Node<std::string>(privData->nativeObj->getPreviousSibling());

	v8::Handle<v8::Function> arbaicaRetCtor = V8Node::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> arbaicaRetObj = v8::Persistent<v8::Object>::New(arbaicaRetCtor->NewInstance());

	struct V8Node::V8NodePrivate* retPrivData = new V8Node::V8NodePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = arbaicaRet;

	arbaicaRetObj->SetInternalField(0, V8DOM::toExternal(retPrivData));
	arbaicaRetObj.MakeWeak(0, V8Node::jsDestructor);
	return arbaicaRetObj;

}

v8::Handle<v8::Value> V8Node::nextSiblingAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8NodePrivate* privData = V8DOM::toClassPtr<V8NodePrivate >(self->GetInternalField(0));

	if (!privData->nativeObj->getNextSibling()) return v8::Undefined();
	Arabica::DOM::Node<std::string>* arbaicaRet = new Arabica::DOM::Node<std::string>(privData->nativeObj->getNextSibling());

	v8::Handle<v8::Function> arbaicaRetCtor = V8Node::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> arbaicaRetObj = v8::Persistent<v8::Object>::New(arbaicaRetCtor->NewInstance());

	struct V8Node::V8NodePrivate* retPrivData = new V8Node::V8NodePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = arbaicaRet;

	arbaicaRetObj->SetInternalField(0, V8DOM::toExternal(retPrivData));
	arbaicaRetObj.MakeWeak(0, V8Node::jsDestructor);
	return arbaicaRetObj;

}

v8::Handle<v8::Value> V8Node::attributesAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8NodePrivate* privData = V8DOM::toClassPtr<V8NodePrivate >(self->GetInternalField(0));


	Arabica::DOM::NamedNodeMap<std::string>* arbaicaRet = new Arabica::DOM::NamedNodeMap<std::string>(privData->nativeObj->getAttributes());

	v8::Handle<v8::Function> arbaicaRetCtor = V8NamedNodeMap::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> arbaicaRetObj = v8::Persistent<v8::Object>::New(arbaicaRetCtor->NewInstance());

	struct V8NamedNodeMap::V8NamedNodeMapPrivate* retPrivData = new V8NamedNodeMap::V8NamedNodeMapPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = arbaicaRet;

	arbaicaRetObj->SetInternalField(0, V8DOM::toExternal(retPrivData));
	arbaicaRetObj.MakeWeak(0, V8NamedNodeMap::jsDestructor);
	return arbaicaRetObj;

}

v8::Handle<v8::Value> V8Node::ownerDocumentAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8NodePrivate* privData = V8DOM::toClassPtr<V8NodePrivate >(self->GetInternalField(0));

	if (!privData->nativeObj->getOwnerDocument()) return v8::Undefined();
	Arabica::DOM::Document<std::string>* arbaicaRet = new Arabica::DOM::Document<std::string>(privData->nativeObj->getOwnerDocument());

	v8::Handle<v8::Function> arbaicaRetCtor = V8Document::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> arbaicaRetObj = v8::Persistent<v8::Object>::New(arbaicaRetCtor->NewInstance());

	struct V8Document::V8DocumentPrivate* retPrivData = new V8Document::V8DocumentPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = arbaicaRet;

	arbaicaRetObj->SetInternalField(0, V8DOM::toExternal(retPrivData));
	arbaicaRetObj.MakeWeak(0, V8Document::jsDestructor);
	return arbaicaRetObj;

}

v8::Handle<v8::Value> V8Node::namespaceURIAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8NodePrivate* privData = V8DOM::toClassPtr<V8NodePrivate >(self->GetInternalField(0));

	return v8::String::New(privData->nativeObj->getNamespaceURI().c_str());
}

v8::Handle<v8::Value> V8Node::prefixAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8NodePrivate* privData = V8DOM::toClassPtr<V8NodePrivate >(self->GetInternalField(0));

	return v8::String::New(privData->nativeObj->getPrefix().c_str());
}

void V8Node::prefixAttrSetter(v8::Local<v8::String> property, v8::Local<v8::Value> value, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8NodePrivate* privData = V8DOM::toClassPtr<V8NodePrivate >(self->GetInternalField(0));
	v8::String::AsciiValue localPrefix(value);
	privData->nativeObj->setPrefix(*localPrefix);
}

v8::Handle<v8::Value> V8Node::localNameAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8NodePrivate* privData = V8DOM::toClassPtr<V8NodePrivate >(self->GetInternalField(0));

	return v8::String::New(privData->nativeObj->getLocalName().c_str());
}
v8::Handle<v8::Value> V8Node::insertBeforeCallback(const v8::Arguments& args) {
	if (args.Length() < 2)
		throw V8Exception("Wrong number of arguments in insertBefore");
	if (!((V8Node::hasInstance(args[0])) && (V8Node::hasInstance(args[1]))))
		throw V8Exception("Parameter mismatch while calling insertBefore");

	v8::Local<v8::Object> self = args.Holder();
	struct V8NodePrivate* privData = V8DOM::toClassPtr<V8NodePrivate >(self->GetInternalField(0));
	Arabica::DOM::Node<std::string>* localNewChild = V8DOM::toClassPtr<V8Node::V8NodePrivate >(args[0]->ToObject()->GetInternalField(0))->nativeObj;
	Arabica::DOM::Node<std::string>* localRefChild = V8DOM::toClassPtr<V8Node::V8NodePrivate >(args[1]->ToObject()->GetInternalField(0))->nativeObj;

	Arabica::DOM::Node<std::string>* retVal = new Arabica::DOM::Node<std::string>(privData->nativeObj->insertBefore(*localNewChild, *localRefChild));
	v8::Handle<v8::Function> retCtor = V8Node::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

	struct V8Node::V8NodePrivate* retPrivData = new V8Node::V8NodePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));

	retObj.MakeWeak(0, V8Node::jsDestructor);
	return retObj;

}

v8::Handle<v8::Value> V8Node::replaceChildCallback(const v8::Arguments& args) {
	if (args.Length() < 2)
		throw V8Exception("Wrong number of arguments in replaceChild");
	if (!((V8Node::hasInstance(args[0])) && (V8Node::hasInstance(args[1]))))
		throw V8Exception("Parameter mismatch while calling replaceChild");

	v8::Local<v8::Object> self = args.Holder();
	struct V8NodePrivate* privData = V8DOM::toClassPtr<V8NodePrivate >(self->GetInternalField(0));
	Arabica::DOM::Node<std::string>* localNewChild = V8DOM::toClassPtr<V8Node::V8NodePrivate >(args[0]->ToObject()->GetInternalField(0))->nativeObj;
	Arabica::DOM::Node<std::string>* localOldChild = V8DOM::toClassPtr<V8Node::V8NodePrivate >(args[1]->ToObject()->GetInternalField(0))->nativeObj;

	Arabica::DOM::Node<std::string>* retVal = new Arabica::DOM::Node<std::string>(privData->nativeObj->replaceChild(*localNewChild, *localOldChild));
	v8::Handle<v8::Function> retCtor = V8Node::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

	struct V8Node::V8NodePrivate* retPrivData = new V8Node::V8NodePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));

	retObj.MakeWeak(0, V8Node::jsDestructor);
	return retObj;

}

v8::Handle<v8::Value> V8Node::removeChildCallback(const v8::Arguments& args) {
	if (args.Length() < 1)
		throw V8Exception("Wrong number of arguments in removeChild");
	if (!(V8Node::hasInstance(args[0])))
		throw V8Exception("Parameter mismatch while calling removeChild");

	v8::Local<v8::Object> self = args.Holder();
	struct V8NodePrivate* privData = V8DOM::toClassPtr<V8NodePrivate >(self->GetInternalField(0));
	Arabica::DOM::Node<std::string>* localOldChild = V8DOM::toClassPtr<V8Node::V8NodePrivate >(args[0]->ToObject()->GetInternalField(0))->nativeObj;

	Arabica::DOM::Node<std::string>* retVal = new Arabica::DOM::Node<std::string>(privData->nativeObj->removeChild(*localOldChild));
	v8::Handle<v8::Function> retCtor = V8Node::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

	struct V8Node::V8NodePrivate* retPrivData = new V8Node::V8NodePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));

	retObj.MakeWeak(0, V8Node::jsDestructor);
	return retObj;

}

v8::Handle<v8::Value> V8Node::appendChildCallback(const v8::Arguments& args) {
	if (args.Length() < 1)
		throw V8Exception("Wrong number of arguments in appendChild");
	if (!(V8Node::hasInstance(args[0])))
		throw V8Exception("Parameter mismatch while calling appendChild");

	v8::Local<v8::Object> self = args.Holder();
	struct V8NodePrivate* privData = V8DOM::toClassPtr<V8NodePrivate >(self->GetInternalField(0));
	Arabica::DOM::Node<std::string>* localNewChild = V8DOM::toClassPtr<V8Node::V8NodePrivate >(args[0]->ToObject()->GetInternalField(0))->nativeObj;

	Arabica::DOM::Node<std::string>* retVal = new Arabica::DOM::Node<std::string>(privData->nativeObj->appendChild(*localNewChild));
	v8::Handle<v8::Function> retCtor = V8Node::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

	struct V8Node::V8NodePrivate* retPrivData = new V8Node::V8NodePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));

	retObj.MakeWeak(0, V8Node::jsDestructor);
	return retObj;

}

v8::Handle<v8::Value> V8Node::hasChildNodesCallback(const v8::Arguments& args) {

	v8::Local<v8::Object> self = args.Holder();
	struct V8NodePrivate* privData = V8DOM::toClassPtr<V8NodePrivate >(self->GetInternalField(0));

	bool retVal = privData->nativeObj->hasChildNodes();

	return v8::Boolean::New(retVal);
}

v8::Handle<v8::Value> V8Node::cloneNodeCallback(const v8::Arguments& args) {
	if (args.Length() < 1)
		throw V8Exception("Wrong number of arguments in cloneNode");

	v8::Local<v8::Object> self = args.Holder();
	struct V8NodePrivate* privData = V8DOM::toClassPtr<V8NodePrivate >(self->GetInternalField(0));
	bool localDeep = args[0]->ToBoolean()->BooleanValue();

	Arabica::DOM::Node<std::string>* retVal = new Arabica::DOM::Node<std::string>(privData->nativeObj->cloneNode(localDeep));
	v8::Handle<v8::Function> retCtor = V8Node::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

	struct V8Node::V8NodePrivate* retPrivData = new V8Node::V8NodePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));

	retObj.MakeWeak(0, V8Node::jsDestructor);
	return retObj;

}

v8::Handle<v8::Value> V8Node::normalizeCallback(const v8::Arguments& args) {

	v8::Local<v8::Object> self = args.Holder();
	struct V8NodePrivate* privData = V8DOM::toClassPtr<V8NodePrivate >(self->GetInternalField(0));

	privData->nativeObj->normalize();

	return v8::Undefined();
}

v8::Handle<v8::Value> V8Node::isSupportedCallback(const v8::Arguments& args) {
	if (args.Length() < 2)
		throw V8Exception("Wrong number of arguments in isSupported");

	v8::Local<v8::Object> self = args.Holder();
	struct V8NodePrivate* privData = V8DOM::toClassPtr<V8NodePrivate >(self->GetInternalField(0));
	v8::String::AsciiValue localFeature(args[0]);
	v8::String::AsciiValue localVersion(args[1]);

	bool retVal = privData->nativeObj->isSupported(*localFeature, *localVersion);

	return v8::Boolean::New(retVal);
}

v8::Handle<v8::Value> V8Node::hasAttributesCallback(const v8::Arguments& args) {

	v8::Local<v8::Object> self = args.Holder();
	struct V8NodePrivate* privData = V8DOM::toClassPtr<V8NodePrivate >(self->GetInternalField(0));

	bool retVal = privData->nativeObj->hasAttributes();

	return v8::Boolean::New(retVal);
}

bool V8Node::hasInstance(v8::Handle<v8::Value> value) {
	return getTmpl()->HasInstance(value);
}

}
}
