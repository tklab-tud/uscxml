/**
 *  @file
 *  @author     2012-2013 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
 *  @copyright  Simplified BSD
 *
 *  @cond
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the FreeBSD license as published by the FreeBSD
 *  project.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 *
 *  You should have received a copy of the FreeBSD license along with this
 *  program. If not, see <http://www.opensource.org/licenses/bsd-license>.
 *  @endcond
 */

#include "V8Document.h"
#include "V8XPathResult.h"
#include "V8Storage.h"

namespace Arabica {
namespace DOM {

v8::Handle<v8::Value> V8Document::localStorageCustomAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	V8DocumentPrivate* privData = V8DOM::toClassPtr<V8DocumentPrivate >(self->GetInternalField(0));

	v8::Handle<v8::Function> retCtor = V8Storage::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

	V8Storage::V8StoragePrivate* retPrivData = new V8Storage::V8StoragePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = privData->dom->storage;

	retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));

	retObj.MakeWeak(0, V8XPathResult::jsDestructor);
	return retObj;

}


v8::Handle<v8::Value> V8Document::evaluateCustomCallback(const v8::Arguments& args) {
	if (args.Length() < 1)
		throw V8Exception("Wrong number of arguments in evaluate");
//  if (!((V8Node::hasInstance(args[1])) && (V8XPathResult::hasInstance(args[3]))))
//    throw V8Exception("Parameter mismatch while calling evaluate");

	v8::Local<v8::Object> self = args.Holder();
	V8DocumentPrivate* privData = V8DOM::toClassPtr<V8DocumentPrivate >(self->GetInternalField(0));

	v8::String::AsciiValue localExpression(args[0]);

	XPath::XPathValue<std::string>* retVal;
	try {
		if (args.Length() > 1) {
			Arabica::DOM::Node<std::string>* localContextNode = V8DOM::toClassPtr<Arabica::DOM::Node<std::string> >(args[1]->ToObject()->GetInternalField(0));
			retVal = new XPath::XPathValue<std::string>(privData->dom->xpath->evaluate(*localExpression, *localContextNode));
		} else {
			retVal = new XPath::XPathValue<std::string>(privData->dom->xpath->evaluate(*localExpression, *privData->nativeObj));
		}
	} catch (std::runtime_error e) {
		std::cout << e.what() << std::endl;
		return v8::Undefined();
	}

	v8::Handle<v8::Function> retCtor = V8XPathResult::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

	V8XPathResult::V8XPathResultPrivate* retPrivData = new V8XPathResult::V8XPathResultPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));

	retObj.MakeWeak(0, V8XPathResult::jsDestructor);
	return retObj;

}

}
}