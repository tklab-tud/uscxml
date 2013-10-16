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

#include "V8NodeList.h"
#include "V8Element.h"
#include "V8Node.h"

namespace Arabica {
namespace DOM {

v8::Handle<v8::Value> V8NodeList::indexedPropertyCustomGetter(uint32_t index, const v8::AccessorInfo &info) {
	v8::Local<v8::Object> self = info.Holder();
	V8NodeListPrivate* privData = V8DOM::toClassPtr<V8NodeListPrivate >(self->GetInternalField(0));

	if (privData->nativeObj->getLength() >= index) {
		switch(privData->nativeObj->item(index).getNodeType()) {
		case Node_base::ELEMENT_NODE: {
			Arabica::DOM::Element<std::string>* retVal = new Arabica::DOM::Element<std::string>(privData->nativeObj->item(index));

			v8::Handle<v8::Function> retCtor = V8Element::getTmpl()->GetFunction();
			v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

			struct V8Element::V8ElementPrivate* retPrivData = new V8Element::V8ElementPrivate();
			retPrivData->dom = privData->dom;
			retPrivData->nativeObj = retVal;

			retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));

			retObj.MakeWeak(0, V8Element::jsDestructor);
			return retObj;
		}
		default: {
			Arabica::DOM::Node<std::string>* retVal = new Arabica::DOM::Node<std::string>(privData->nativeObj->item(index));

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

	return v8::Undefined();

}

}
}