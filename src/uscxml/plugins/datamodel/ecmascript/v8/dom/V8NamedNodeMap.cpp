#include "V8NamedNodeMap.h"
#include "V8Node.h"

namespace Arabica {
namespace DOM {

v8::Persistent<v8::FunctionTemplate> V8NamedNodeMap::Tmpl;


v8::Handle<v8::Value> V8NamedNodeMap::lengthAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8NamedNodeMapPrivate* privData = V8DOM::toClassPtr<V8NamedNodeMapPrivate >(self->GetInternalField(0));

	return v8::Integer::New(privData->nativeObj->getLength());
}
v8::Handle<v8::Value> V8NamedNodeMap::getNamedItemCallback(const v8::Arguments& args) {
	if (args.Length() < 1)
		throw V8Exception("Wrong number of arguments in getNamedItem");

	v8::Local<v8::Object> self = args.Holder();
	struct V8NamedNodeMapPrivate* privData = V8DOM::toClassPtr<V8NamedNodeMapPrivate >(self->GetInternalField(0));
	v8::String::AsciiValue localName(args[0]);

	Arabica::DOM::Node<std::string>* retVal = new Arabica::DOM::Node<std::string>(privData->nativeObj->getNamedItem(*localName));
	v8::Handle<v8::Function> retCtor = V8Node::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

	struct V8Node::V8NodePrivate* retPrivData = new V8Node::V8NodePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));

	retObj.MakeWeak(0, V8Node::jsDestructor);
	return retObj;

}

v8::Handle<v8::Value> V8NamedNodeMap::setNamedItemCallback(const v8::Arguments& args) {
	if (args.Length() < 1)
		throw V8Exception("Wrong number of arguments in setNamedItem");
	if (!(V8Node::hasInstance(args[0])))
		throw V8Exception("Parameter mismatch while calling setNamedItem");

	v8::Local<v8::Object> self = args.Holder();
	struct V8NamedNodeMapPrivate* privData = V8DOM::toClassPtr<V8NamedNodeMapPrivate >(self->GetInternalField(0));
	Arabica::DOM::Node<std::string>* localArg = V8DOM::toClassPtr<V8Node::V8NodePrivate >(args[0]->ToObject()->GetInternalField(0))->nativeObj;

	Arabica::DOM::Node<std::string>* retVal = new Arabica::DOM::Node<std::string>(privData->nativeObj->setNamedItem(*localArg));
	v8::Handle<v8::Function> retCtor = V8Node::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

	struct V8Node::V8NodePrivate* retPrivData = new V8Node::V8NodePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));

	retObj.MakeWeak(0, V8Node::jsDestructor);
	return retObj;

}

v8::Handle<v8::Value> V8NamedNodeMap::removeNamedItemCallback(const v8::Arguments& args) {
	if (args.Length() < 1)
		throw V8Exception("Wrong number of arguments in removeNamedItem");

	v8::Local<v8::Object> self = args.Holder();
	struct V8NamedNodeMapPrivate* privData = V8DOM::toClassPtr<V8NamedNodeMapPrivate >(self->GetInternalField(0));
	v8::String::AsciiValue localName(args[0]);

	Arabica::DOM::Node<std::string>* retVal = new Arabica::DOM::Node<std::string>(privData->nativeObj->removeNamedItem(*localName));
	v8::Handle<v8::Function> retCtor = V8Node::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

	struct V8Node::V8NodePrivate* retPrivData = new V8Node::V8NodePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));

	retObj.MakeWeak(0, V8Node::jsDestructor);
	return retObj;

}

v8::Handle<v8::Value> V8NamedNodeMap::itemCallback(const v8::Arguments& args) {
	if (args.Length() < 1)
		throw V8Exception("Wrong number of arguments in item");

	v8::Local<v8::Object> self = args.Holder();
	struct V8NamedNodeMapPrivate* privData = V8DOM::toClassPtr<V8NamedNodeMapPrivate >(self->GetInternalField(0));
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

v8::Handle<v8::Value> V8NamedNodeMap::getNamedItemNSCallback(const v8::Arguments& args) {
	if (args.Length() < 2)
		throw V8Exception("Wrong number of arguments in getNamedItemNS");

	v8::Local<v8::Object> self = args.Holder();
	struct V8NamedNodeMapPrivate* privData = V8DOM::toClassPtr<V8NamedNodeMapPrivate >(self->GetInternalField(0));
	v8::String::AsciiValue localNamespaceURI(args[0]);
	v8::String::AsciiValue localLocalName(args[1]);

	Arabica::DOM::Node<std::string>* retVal = new Arabica::DOM::Node<std::string>(privData->nativeObj->getNamedItemNS(*localNamespaceURI, *localLocalName));
	v8::Handle<v8::Function> retCtor = V8Node::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

	struct V8Node::V8NodePrivate* retPrivData = new V8Node::V8NodePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));

	retObj.MakeWeak(0, V8Node::jsDestructor);
	return retObj;

}

v8::Handle<v8::Value> V8NamedNodeMap::setNamedItemNSCallback(const v8::Arguments& args) {
	if (args.Length() < 1)
		throw V8Exception("Wrong number of arguments in setNamedItemNS");
	if (!(V8Node::hasInstance(args[0])))
		throw V8Exception("Parameter mismatch while calling setNamedItemNS");

	v8::Local<v8::Object> self = args.Holder();
	struct V8NamedNodeMapPrivate* privData = V8DOM::toClassPtr<V8NamedNodeMapPrivate >(self->GetInternalField(0));
	Arabica::DOM::Node<std::string>* localArg = V8DOM::toClassPtr<V8Node::V8NodePrivate >(args[0]->ToObject()->GetInternalField(0))->nativeObj;

	Arabica::DOM::Node<std::string>* retVal = new Arabica::DOM::Node<std::string>(privData->nativeObj->setNamedItemNS(*localArg));
	v8::Handle<v8::Function> retCtor = V8Node::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

	struct V8Node::V8NodePrivate* retPrivData = new V8Node::V8NodePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));

	retObj.MakeWeak(0, V8Node::jsDestructor);
	return retObj;

}

v8::Handle<v8::Value> V8NamedNodeMap::removeNamedItemNSCallback(const v8::Arguments& args) {
	if (args.Length() < 2)
		throw V8Exception("Wrong number of arguments in removeNamedItemNS");

	v8::Local<v8::Object> self = args.Holder();
	struct V8NamedNodeMapPrivate* privData = V8DOM::toClassPtr<V8NamedNodeMapPrivate >(self->GetInternalField(0));
	v8::String::AsciiValue localNamespaceURI(args[0]);
	v8::String::AsciiValue localLocalName(args[1]);

	Arabica::DOM::Node<std::string>* retVal = new Arabica::DOM::Node<std::string>(privData->nativeObj->removeNamedItemNS(*localNamespaceURI, *localLocalName));
	v8::Handle<v8::Function> retCtor = V8Node::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

	struct V8Node::V8NodePrivate* retPrivData = new V8Node::V8NodePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));

	retObj.MakeWeak(0, V8Node::jsDestructor);
	return retObj;

}

bool V8NamedNodeMap::hasInstance(v8::Handle<v8::Value> value) {
	return getTmpl()->HasInstance(value);
}

}
}
