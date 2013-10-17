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

#include "V8Node.h"
#include "V8NamedNodeMap.h"

namespace Arabica {
namespace DOM {

v8::Handle<v8::Value> V8Node::attributesCustomAttrGetter(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	v8::Local<v8::Object> self = info.Holder();
	struct V8NodePrivate* privData = V8DOM::toClassPtr<V8NodePrivate >(self->GetInternalField(0));

	if (!privData->nativeObj->hasAttributes()) {
		return v8::Undefined();
	}

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

}
}