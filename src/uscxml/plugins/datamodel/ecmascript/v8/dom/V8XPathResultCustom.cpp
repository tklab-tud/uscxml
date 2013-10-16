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

#include "V8XPathResult.h"
#include "V8Node.h"

namespace Arabica {
namespace DOM {

v8::Handle<v8::Value> V8XPathResult::singleNodeValueCustomAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	V8XPathResultPrivate* privData = V8DOM::toClassPtr<V8XPathResultPrivate >(self->GetInternalField(0));

	Arabica::DOM::Node<std::string>* retVal = new Arabica::DOM::Node<std::string>(privData->nativeObj->asNodeSet()[0]);

	v8::Handle<v8::Function> retCtor = V8Node::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

	struct V8Node::V8NodePrivate* retPrivData = new V8Node::V8NodePrivate();
	retPrivData->dom = privData->dom;
	retPrivData->nativeObj = retVal;

	retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));

	retObj.MakeWeak(0, V8Node::jsDestructor);
	return retObj;
}

}
}