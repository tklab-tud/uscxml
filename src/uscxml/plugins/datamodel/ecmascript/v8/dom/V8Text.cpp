#include "V8CharacterData.h"
#include "V8Text.h"

namespace Arabica {
namespace DOM {

v8::Persistent<v8::FunctionTemplate> V8Text::Tmpl;

v8::Handle<v8::Value> V8Text::splitTextCallback(const v8::Arguments& args) {
	if (args.Length() < 1)
		throw V8Exception("Wrong number of arguments in splitText");

	v8::Local<v8::Object> self = args.Holder();
	struct V8TextPrivate* privData = V8DOM::toClassPtr<V8TextPrivate >(self->GetInternalField(0));
	unsigned long localOffset = args[0]->ToNumber()->Uint32Value();

	Arabica::DOM::Text<std::string>* retVal = new Arabica::DOM::Text<std::string>(privData->arabicaThis->splitText(localOffset));
	v8::Handle<v8::Function> retCtor = V8Text::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

	struct V8Text::V8TextPrivate* retPrivData = new V8Text::V8TextPrivate();
	retPrivData->dom = privData->dom;
	retPrivData->arabicaThis = retVal;

	retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));

	retObj.MakeWeak(0, V8Text::jsDestructor);
	return retObj;

}

bool V8Text::hasInstance(v8::Handle<v8::Value> value) {
	return getTmpl()->HasInstance(value);
}

}
}
