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

	return v8::String::New(privData->arabicaThis->getTagName().c_str());
}
v8::Handle<v8::Value> V8Element::getAttributeCallback(const v8::Arguments& args) {
	if (args.Length() < 1)
		throw V8Exception("Wrong number of arguments in getAttribute");

	v8::Local<v8::Object> self = args.Holder();
	struct V8ElementPrivate* privData = V8DOM::toClassPtr<V8ElementPrivate >(self->GetInternalField(0));
	v8::String::AsciiValue localName(args[0]);

	std::string retVal = privData->arabicaThis->getAttribute(*localName);

	return v8::String::New(retVal.c_str());
}

v8::Handle<v8::Value> V8Element::setAttributeCallback(const v8::Arguments& args) {
	if (args.Length() < 2)
		throw V8Exception("Wrong number of arguments in setAttribute");

	v8::Local<v8::Object> self = args.Holder();
	struct V8ElementPrivate* privData = V8DOM::toClassPtr<V8ElementPrivate >(self->GetInternalField(0));
	v8::String::AsciiValue localName(args[0]);
	v8::String::AsciiValue localValue(args[1]);

	privData->arabicaThis->setAttribute(*localName, *localValue);

	return v8::Undefined();
}

v8::Handle<v8::Value> V8Element::removeAttributeCallback(const v8::Arguments& args) {
	if (args.Length() < 1)
		throw V8Exception("Wrong number of arguments in removeAttribute");

	v8::Local<v8::Object> self = args.Holder();
	struct V8ElementPrivate* privData = V8DOM::toClassPtr<V8ElementPrivate >(self->GetInternalField(0));
	v8::String::AsciiValue localName(args[0]);

	privData->arabicaThis->removeAttribute(*localName);

	return v8::Undefined();
}

v8::Handle<v8::Value> V8Element::getAttributeNodeCallback(const v8::Arguments& args) {
	if (args.Length() < 1)
		throw V8Exception("Wrong number of arguments in getAttributeNode");

	v8::Local<v8::Object> self = args.Holder();
	struct V8ElementPrivate* privData = V8DOM::toClassPtr<V8ElementPrivate >(self->GetInternalField(0));
	v8::String::AsciiValue localName(args[0]);

	Arabica::DOM::Attr<std::string>* retVal = new Arabica::DOM::Attr<std::string>(privData->arabicaThis->getAttributeNode(*localName));
	v8::Handle<v8::Function> retCtor = V8Attr::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

	struct V8Attr::V8AttrPrivate* retPrivData = new V8Attr::V8AttrPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->arabicaThis = retVal;

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
	Arabica::DOM::Attr<std::string>* localNewAttr = V8DOM::toClassPtr<V8Attr::V8AttrPrivate >(args[0]->ToObject()->GetInternalField(0))->arabicaThis;

	Arabica::DOM::Attr<std::string>* retVal = new Arabica::DOM::Attr<std::string>(privData->arabicaThis->setAttributeNode(*localNewAttr));
	v8::Handle<v8::Function> retCtor = V8Attr::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

	struct V8Attr::V8AttrPrivate* retPrivData = new V8Attr::V8AttrPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->arabicaThis = retVal;

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
	Arabica::DOM::Attr<std::string>* localOldAttr = V8DOM::toClassPtr<V8Attr::V8AttrPrivate >(args[0]->ToObject()->GetInternalField(0))->arabicaThis;

	Arabica::DOM::Attr<std::string>* retVal = new Arabica::DOM::Attr<std::string>(privData->arabicaThis->removeAttributeNode(*localOldAttr));
	v8::Handle<v8::Function> retCtor = V8Attr::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

	struct V8Attr::V8AttrPrivate* retPrivData = new V8Attr::V8AttrPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->arabicaThis = retVal;

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

	Arabica::DOM::NodeList<std::string>* retVal = new Arabica::DOM::NodeList<std::string>(privData->arabicaThis->getElementsByTagName(*localName));
	v8::Handle<v8::Function> retCtor = V8NodeList::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

	struct V8NodeList::V8NodeListPrivate* retPrivData = new V8NodeList::V8NodeListPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->arabicaThis = retVal;

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

	std::string retVal = privData->arabicaThis->getAttributeNS(*localNamespaceURI, *localLocalName);

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

	privData->arabicaThis->setAttributeNS(*localNamespaceURI, *localQualifiedName, *localValue);

	return v8::Undefined();
}

v8::Handle<v8::Value> V8Element::removeAttributeNSCallback(const v8::Arguments& args) {
	if (args.Length() < 2)
		throw V8Exception("Wrong number of arguments in removeAttributeNS");

	v8::Local<v8::Object> self = args.Holder();
	struct V8ElementPrivate* privData = V8DOM::toClassPtr<V8ElementPrivate >(self->GetInternalField(0));
	v8::String::AsciiValue localNamespaceURI(args[0]);
	v8::String::AsciiValue localLocalName(args[1]);

	privData->arabicaThis->removeAttributeNS(*localNamespaceURI, *localLocalName);

	return v8::Undefined();
}

v8::Handle<v8::Value> V8Element::getAttributeNodeNSCallback(const v8::Arguments& args) {
	if (args.Length() < 2)
		throw V8Exception("Wrong number of arguments in getAttributeNodeNS");

	v8::Local<v8::Object> self = args.Holder();
	struct V8ElementPrivate* privData = V8DOM::toClassPtr<V8ElementPrivate >(self->GetInternalField(0));
	v8::String::AsciiValue localNamespaceURI(args[0]);
	v8::String::AsciiValue localLocalName(args[1]);

	Arabica::DOM::Attr<std::string>* retVal = new Arabica::DOM::Attr<std::string>(privData->arabicaThis->getAttributeNodeNS(*localNamespaceURI, *localLocalName));
	v8::Handle<v8::Function> retCtor = V8Attr::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

	struct V8Attr::V8AttrPrivate* retPrivData = new V8Attr::V8AttrPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->arabicaThis = retVal;

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
	Arabica::DOM::Attr<std::string>* localNewAttr = V8DOM::toClassPtr<V8Attr::V8AttrPrivate >(args[0]->ToObject()->GetInternalField(0))->arabicaThis;

	Arabica::DOM::Attr<std::string>* retVal = new Arabica::DOM::Attr<std::string>(privData->arabicaThis->setAttributeNodeNS(*localNewAttr));
	v8::Handle<v8::Function> retCtor = V8Attr::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

	struct V8Attr::V8AttrPrivate* retPrivData = new V8Attr::V8AttrPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->arabicaThis = retVal;

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

	Arabica::DOM::NodeList<std::string>* retVal = new Arabica::DOM::NodeList<std::string>(privData->arabicaThis->getElementsByTagNameNS(*localNamespaceURI, *localLocalName));
	v8::Handle<v8::Function> retCtor = V8NodeList::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

	struct V8NodeList::V8NodeListPrivate* retPrivData = new V8NodeList::V8NodeListPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->arabicaThis = retVal;

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

	bool retVal = privData->arabicaThis->hasAttribute(*localName);

	return v8::Boolean::New(retVal);
}

v8::Handle<v8::Value> V8Element::hasAttributeNSCallback(const v8::Arguments& args) {
	if (args.Length() < 2)
		throw V8Exception("Wrong number of arguments in hasAttributeNS");

	v8::Local<v8::Object> self = args.Holder();
	struct V8ElementPrivate* privData = V8DOM::toClassPtr<V8ElementPrivate >(self->GetInternalField(0));
	v8::String::AsciiValue localNamespaceURI(args[0]);
	v8::String::AsciiValue localLocalName(args[1]);

	bool retVal = privData->arabicaThis->hasAttributeNS(*localNamespaceURI, *localLocalName);

	return v8::Boolean::New(retVal);
}

bool V8Element::hasInstance(v8::Handle<v8::Value> value) {
	return getTmpl()->HasInstance(value);
}

}
}
