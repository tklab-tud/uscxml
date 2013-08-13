#include "uscxml/Common.h"
#include "V8DataModel.h"
#include "dom/V8DOM.h"
#include "dom/V8Document.h"
#include "dom/V8Node.h"
#include "dom/V8SCXMLEvent.h"

#include "uscxml/Message.h"
#include <glog/logging.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

using namespace Arabica::XPath;
using namespace Arabica::DOM;

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool connect(pluma::Host& host) {
	host.add( new V8DataModelProvider() );
	return true;
}
#endif

V8DataModel::V8DataModel() {
//  _contexts.push_back(v8::Context::New());
}

boost::shared_ptr<DataModelImpl> V8DataModel::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<V8DataModel> dm = boost::shared_ptr<V8DataModel>(new V8DataModel());
	dm->_interpreter = interpreter;
	v8::Locker locker;
	v8::HandleScope scope;

	dm->_dom = new V8DOM();
//  dom->interpreter = interpreter;
	dm->_dom->xpath = new XPath<std::string>();
	dm->_dom->xpath->setNamespaceContext(interpreter->getNSContext());

	// see http://stackoverflow.com/questions/3171418/v8-functiontemplate-class-instance

	// some free functions
	v8::Handle<v8::ObjectTemplate> global = v8::ObjectTemplate::New();
	global->Set(v8::String::New("In"), v8::FunctionTemplate::New(jsIn, v8::External::New(reinterpret_cast<void*>(dm.get()))), v8::ReadOnly);
	global->Set(v8::String::New("print"), v8::FunctionTemplate::New(jsPrint, v8::External::New(reinterpret_cast<void*>(dm.get()))), v8::ReadOnly);

	v8::Persistent<v8::Context> context = v8::Context::New(0, global);
	v8::Context::Scope contextScope(context);

	// instantiate the document function
	v8::Handle<v8::Function> docCtor = V8Document::getTmpl()->GetFunction();
	v8::Handle<v8::Object> docObj = docCtor->NewInstance();

	V8Document::V8DocumentPrivate* privData = new V8Document::V8DocumentPrivate();
	privData->nativeObj = new Document<std::string>(interpreter->getDocument());
	privData->dom = dm->_dom;
	docObj->SetInternalField(0, V8DOM::toExternal(privData));

	context->Global()->Set(v8::String::New("document"), docObj);

	context->Global()->SetAccessor(v8::String::New("_sessionid"),
	                               V8DataModel::getAttribute,
	                               V8DataModel::setWithException,
	                               v8::String::New(interpreter->getSessionId().c_str()));
	context->Global()->SetAccessor(v8::String::New("_name"),
	                               V8DataModel::getAttribute,
	                               V8DataModel::setWithException,
	                               v8::String::New(interpreter->getName().c_str()));
	context->Global()->SetAccessor(v8::String::New("_ioprocessors"),
	                               V8DataModel::getIOProcessors,
	                               V8DataModel::setWithException,
	                               v8::External::New(reinterpret_cast<void*>(dm.get())));

	dm->_contexts.push_back(context);

	// instantiate objects - we have to have a context for that!
	dm->eval(Element<std::string>(), "_invokers = {};");
	dm->eval(Element<std::string>(), "_x = {};");

	return dm;
}

v8::Handle<v8::Value> V8DataModel::getAttribute(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	return info.Data();
}

void V8DataModel::setWithException(v8::Local<v8::String> property, v8::Local<v8::Value> value, const v8::AccessorInfo& info) {
	v8::String::AsciiValue data(property);
	std::string msg = "Cannot set " + std::string(*data);
	v8::ThrowException(v8::Exception::ReferenceError(v8::String::New(msg.c_str())));
}

v8::Handle<v8::Value> V8DataModel::getIOProcessors(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	V8DataModel* dataModel = V8DOM::toClassPtr<V8DataModel>(info.Data());

	if (dataModel->_ioProcessors.IsEmpty()) {
		dataModel->_ioProcessors = v8::Persistent<v8::Object>::New(v8::Object::New());
		//v8::Handle<v8::Object> ioProcessorObj = v8::Object::New();
		std::map<std::string, IOProcessor> ioProcessors = dataModel->_interpreter->getIOProcessors();
		std::map<std::string, IOProcessor>::const_iterator ioProcIter = ioProcessors.begin();
		while(ioProcIter != ioProcessors.end()) {
//			std::cout << ioProcIter->first << std::endl;
			dataModel->_ioProcessors->Set(v8::String::New(ioProcIter->first.c_str()),
			                              dataModel->getDataAsValue(ioProcIter->second.getDataModelVariables()));
			ioProcIter++;
		}
	}
	return dataModel->_ioProcessors;
}

V8DataModel::~V8DataModel() {
	while(_contexts.size() > 0) {
		_contexts.back().Dispose();
		_contexts.pop_back();
	}
}

void V8DataModel::pushContext() {
	_contexts.push_back(_contexts.back().New(_contexts.back()));
}

void V8DataModel::popContext() {
	if (_contexts.size() > 1) {
		_contexts.back().Dispose();
		_contexts.pop_back();
	}
}

void V8DataModel::initialize() {
}

void V8DataModel::setEvent(const Event& event) {
	v8::Locker locker;
	v8::HandleScope handleScope;
	v8::Context::Scope contextScope(_contexts.front());
	v8::Handle<v8::Object> global = _contexts.front()->Global();

	v8::Handle<v8::Function> eventCtor = V8SCXMLEvent::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> eventObj = v8::Persistent<v8::Object>::New(eventCtor->NewInstance());

	V8SCXMLEvent::V8SCXMLEventPrivate* privData = new V8SCXMLEvent::V8SCXMLEventPrivate();
	privData->nativeObj = new Event(event);
	privData->dom = _dom;
	eventObj->SetInternalField(0, V8DOM::toExternal(privData));
	eventObj.MakeWeak(0, V8SCXMLEvent::jsDestructor);

	if (event.dom) {
		eventObj->Set(v8::String::New("data"), getDocumentAsValue(event.dom));
	} else if (event.content.length() > 0) {
		// _event.data is a string or JSON
		Data json = Data::fromJSON(event.content);
		if (json) {
			eventObj->Set(v8::String::New("data"), getDataAsValue(json));
		} else {
			eventObj->Set(v8::String::New("data"), v8::String::New(Interpreter::spaceNormalize(event.content).c_str()));
		}
	} else {
		// _event.data is KVP
		Event eventCopy(event);
		if (!eventCopy.params.empty()) {
			Event::params_t::iterator paramIter = eventCopy.params.begin();
			while(paramIter != eventCopy.params.end()) {
				eventCopy.data.compound[paramIter->first] = Data(paramIter->second, Data::VERBATIM);
				paramIter++;
			}
		}
		if (!eventCopy.namelist.empty()) {
			Event::namelist_t::iterator nameListIter = eventCopy.namelist.begin();
			while(nameListIter != eventCopy.namelist.end()) {
				eventCopy.data.compound[nameListIter->first] = Data(nameListIter->second, Data::VERBATIM);
				nameListIter++;
			}
		}
		if (eventCopy.data) {
			eventObj->Set(v8::String::New("data"), getDataAsValue(eventCopy.data)); // set data part of _event
		} else {
			// test 343 / test 488
			eventObj->Set(v8::String::New("data"), v8::Undefined()); // set data part of _event
		}
	}
	// we cannot make _event v8::ReadOnly as it will ignore subsequent setEvents
	global->Set(v8::String::New("_event"), eventObj);
}

Data V8DataModel::getStringAsData(const std::string& content) {
	v8::Locker locker;
	v8::HandleScope handleScope;
	v8::Context::Scope contextScope(_contexts.front());
	v8::Handle<v8::Value> result = evalAsValue(content);
	Data data = getValueAsData(result);
	return data;
}

Data V8DataModel::getValueAsData(const v8::Handle<v8::Value>& value) {
	std::set<v8::Value*> foo = std::set<v8::Value*>();
	return getValueAsData(value, foo);
}

Data V8DataModel::getValueAsData(const v8::Handle<v8::Value>& value, std::set<v8::Value*>& alreadySeen) {
	Data data;

	/// TODO: Breaking cycles does not work yet
	if (alreadySeen.find(*value) != alreadySeen.end())
		return data;
	alreadySeen.insert(*value);

	if (false) {
	} else if (value->IsArray()) {
		v8::Handle<v8::Array> array = v8::Handle<v8::Array>::Cast(value);
		for (int i = 0; i < array->Length(); i++) {
			data.array.push_back(getValueAsData(array->Get(i), alreadySeen));
		}
	} else if (value->IsBoolean()) {
		data.atom = (value->ToBoolean()->Value() ? "true" : "false");
	} else if (value->IsBooleanObject()) {
		LOG(ERROR) << "IsBooleanObject is unimplemented" << std::endl;
	} else if (value->IsDate()) {
		LOG(ERROR) << "IsDate is unimplemented" << std::endl;
	} else if (value->IsExternal()) {
		LOG(ERROR) << "IsExternal is unimplemented" << std::endl;
	} else if (value->IsFalse()) {
		LOG(ERROR) << "IsFalse is unimplemented" << std::endl;
	} else if (value->IsFunction()) {
		LOG(ERROR) << "IsFunction is unimplemented" << std::endl;
	} else if (value->IsInt32()) {
		int32_t prop = value->Int32Value();
		data.atom = toStr(prop);
	} else if (value->IsNativeError()) {
		LOG(ERROR) << "IsNativeError is unimplemented" << std::endl;
	} else if (value->IsNull()) {
		LOG(ERROR) << "IsNull is unimplemented" << std::endl;
	} else if (value->IsNumber()) {
		v8::String::AsciiValue prop(v8::Handle<v8::String>::Cast(v8::Handle<v8::Number>::Cast(value)));
		data.atom = *prop;
	} else if (value->IsNumberObject()) {
		LOG(ERROR) << "IsNumberObject is unimplemented" << std::endl;
	} else if (value->IsObject()) {
		v8::Handle<v8::Object> object = v8::Handle<v8::Object>::Cast(value);
		v8::Local<v8::Array> properties = object->GetPropertyNames();
		for (int i = 0; i < properties->Length(); i++) {
			assert(properties->Get(i)->IsString());
			v8::String::AsciiValue key(v8::Handle<v8::String>::Cast(properties->Get(i)));
			v8::Local<v8::Value> property = object->Get(properties->Get(i));
			data.compound[*key] = getValueAsData(property, alreadySeen);
		}
	} else if (value->IsRegExp()) {
		LOG(ERROR) << "IsRegExp is unimplemented" << std::endl;
	} else if(value->IsString()) {
		v8::String::AsciiValue property(v8::Handle<v8::String>::Cast(value));
		data.atom = *property;
		data.type = Data::VERBATIM;
	} else if(value->IsStringObject()) {
		LOG(ERROR) << "IsStringObject is unimplemented" << std::endl;
	} else if(value->IsTrue()) {
		LOG(ERROR) << "IsTrue is unimplemented" << std::endl;
	} else if(value->IsUint32()) {
		LOG(ERROR) << "IsUint32 is unimplemented" << std::endl;
	} else if(value->IsUndefined()) {
		data.atom = "undefined";
	}
	return data;
}

v8::Handle<v8::Value> V8DataModel::getDocumentAsValue(const Document<std::string>& doc) {
	v8::Handle<v8::Function> retCtor = V8Document::getTmpl()->GetFunction();
	v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

	struct V8Document::V8DocumentPrivate* retPrivData = new V8Document::V8DocumentPrivate();
	retPrivData->dom = _dom;
	retPrivData->nativeObj = new Document<std::string>(doc);

	retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));
	retObj.MakeWeak(0, V8Document::jsDestructor);

	return retObj;
}

v8::Handle<v8::Value> V8DataModel::getDataAsValue(const Data& data) {
	if (data.compound.size() > 0) {
		v8::Handle<v8::Object> value = v8::Object::New();
		std::map<std::string, Data>::const_iterator compoundIter = data.compound.begin();
		while(compoundIter != data.compound.end()) {
			value->Set(v8::String::New(compoundIter->first.c_str()), getDataAsValue(compoundIter->second));
			compoundIter++;
		}
		return value;
	}
	if (data.array.size() > 0) {
		v8::Handle<v8::Object> value = v8::Array::New();
		std::list<Data>::const_iterator arrayIter = data.array.begin();
		uint32_t index = 0;
		while(arrayIter != data.array.end()) {
			value->Set(index++, getDataAsValue(*arrayIter));
			arrayIter++;
		}
		return value;
	}
	if (data.type == Data::VERBATIM) {
		return v8::String::New(data.atom.c_str());
	} else {
		return evalAsValue(data.atom);
	}
}

v8::Handle<v8::Value> V8DataModel::jsPrint(const v8::Arguments& args) {
	if (args.Length() > 0) {
		v8::String::AsciiValue printMsg(args[0]->ToString());
		std::cout << *printMsg;
	}
	return v8::Undefined();
}

v8::Handle<v8::Value> V8DataModel::jsIn(const v8::Arguments& args) {
	V8DataModel* INSTANCE = static_cast<V8DataModel*>(v8::External::Unwrap(args.Data()));
	for (unsigned int i = 0; i < args.Length(); i++) {
		if (args[i]->IsString()) {
			std::string stateName(*v8::String::AsciiValue(args[i]->ToString()));
			if (Interpreter::isMember(INSTANCE->_interpreter->getState(stateName), INSTANCE->_interpreter->getConfiguration())) {
				continue;
			}
		}
		return v8::Boolean::New(false);
	}
	return v8::Boolean::New(true);
}

bool V8DataModel::validate(const std::string& location, const std::string& schema) {
	return true;
}

uint32_t V8DataModel::getLength(const std::string& expr) {
	v8::Locker locker;
	v8::HandleScope handleScope;
	v8::TryCatch tryCatch;
	v8::Context::Scope contextScope(_contexts.back());
	v8::Handle<v8::Value> result = evalAsValue(expr);
	if (!result.IsEmpty() && result->IsArray())
		return result.As<v8::Array>()->Length();

	Event exceptionEvent;
	exceptionEvent.name = "error.execution";
	exceptionEvent.data.compound["exception"] = Data("'" + expr + "' does not evaluate to an array.", Data::VERBATIM);

	throw(exceptionEvent);
}

void V8DataModel::setForeach(const std::string& item,
                             const std::string& array,
                             const std::string& index,
                             uint32_t iteration) {
	if (!isDeclared(item)) {
		assign(item, Data());
	}
	// assign array element to item
	std::stringstream ss;
	ss << array << "[" << iteration << "]";
	assign(item, ss.str());
	if (index.length() > 0) {
		// assign iteration element to index
		std::stringstream ss;
		ss << iteration;
		assign(index, ss.str());
	}
}

void V8DataModel::eval(const Element<std::string>& scriptElem,
                       const std::string& expr) {
	v8::Locker locker;
	v8::HandleScope handleScope;
	v8::Context::Scope contextScope(_contexts.back());
	evalAsValue(expr);
}

bool V8DataModel::isDeclared(const std::string& expr) {
	/**
	 * Undeclared variables can be checked by trying to access them and catching
	 * a reference error.
	 */

	v8::Locker locker;
	v8::HandleScope handleScope;
	v8::Context::Scope contextScope(_contexts.back());

	v8::TryCatch tryCatch;
	v8::Handle<v8::String> source = v8::String::New(expr.c_str());
	v8::Handle<v8::Script> script = v8::Script::Compile(source);

	v8::Handle<v8::Value> result;
	if (!script.IsEmpty())
		result = script->Run();

	if (result.IsEmpty())
		return false;

	return true;
}

bool V8DataModel::evalAsBool(const std::string& expr) {
	v8::Locker locker;
	v8::HandleScope handleScope;
	v8::Context::Scope contextScope(_contexts.back());
	v8::Handle<v8::Value> result = evalAsValue(expr);
	return(result->ToBoolean()->BooleanValue());
}

std::string V8DataModel::evalAsString(const std::string& expr) {
	v8::Locker locker;
	v8::HandleScope handleScope;
	v8::Context::Scope contextScope(_contexts.back());
	v8::Handle<v8::Value> result = evalAsValue(expr);
	if (result->IsObject()) {
		v8::Local<v8::Object> obj = result->ToObject();
		v8::Local<v8::Object> proto;

		proto = obj->FindInstanceInPrototypeChain(V8Document::getTmpl());
		if (!proto.IsEmpty()) {
			struct V8Document::V8DocumentPrivate* privData =
			    V8DOM::toClassPtr<V8Document::V8DocumentPrivate >(obj->GetInternalField(0));
			std::stringstream ss;
			ss << privData->nativeObj->getDocumentElement();
			return ss.str();
		}

		proto = obj->FindInstanceInPrototypeChain(V8Node::getTmpl());
		if (!proto.IsEmpty()) {
			struct V8Node::V8NodePrivate* privData =
			    V8DOM::toClassPtr<V8Node::V8NodePrivate >(obj->GetInternalField(0));
			std::stringstream ss;
			ss << privData->nativeObj;
			return ss.str();
		}

		Data data = getValueAsData(result);
		return toStr(data);
	}
	if (result->IsNumber()) {
		return toStr(result->ToNumber()->NumberValue());
	}
	v8::String::AsciiValue data(result->ToString());
	return std::string(*data);
}

double V8DataModel::evalAsNumber(const std::string& expr) {
	v8::Locker locker;
	v8::HandleScope handleScope;
	v8::Context::Scope contextScope(_contexts.back());
	v8::Handle<v8::Value> result = evalAsValue(expr);
	if (result->IsNumber()) {
		return result->ToNumber()->NumberValue();
	}
	return 0;
}

void V8DataModel::assign(const Element<std::string>& assignElem,
                         const Document<std::string>& doc,
                         const std::string& content) {
	v8::Locker locker;
	v8::HandleScope handleScope;
	v8::Context::Scope contextScope(_contexts.front());
	v8::Handle<v8::Object> global = _contexts.front()->Global();

	std::string key;
	if (HAS_ATTR(assignElem, "id")) {
		key = ATTR(assignElem, "id");
	} else if (HAS_ATTR(assignElem, "location")) {
		key = ATTR(assignElem, "location");
	}
	if (key.length() == 0)
		throw Event("error.execution", Event::PLATFORM);

	if (HAS_ATTR(assignElem, "expr")) {
		evalAsValue(key + " = " + ATTR(assignElem, "expr"));
	} else if (doc) {
		global->Set(v8::String::New(key.c_str()), getDocumentAsValue(doc));
	} else if (content.size() > 0) {
		try {
			evalAsValue(key + " = " + content);
		} catch (...) {
			evalAsValue(key + " = " + "\"" + Interpreter::spaceNormalize(content) + "\"");
		}
	} else {
		global->Set(v8::String::New(key.c_str()), v8::Undefined());
	}
}

void V8DataModel::assign(const std::string& location,
                         const Data& data) {
	v8::Locker locker;
	v8::HandleScope handleScope;
	v8::Context::Scope contextScope(_contexts.front());

	std::stringstream ssJSON;
	ssJSON << data;
	evalAsValue(location + " = " + ssJSON.str());
}

void V8DataModel::init(const Element<std::string>& dataElem,
                       const Document<std::string>& doc,
                       const std::string& content) {
	try {
		assign(dataElem, doc, content);
	} catch (Event e) {
		// test 277
		std::string key;
		if (HAS_ATTR(dataElem, "id")) {
			key = ATTR(dataElem, "id");
		} else if (HAS_ATTR(dataElem, "location")) {
			key = ATTR(dataElem, "location");
		}
		v8::Locker locker;
		v8::HandleScope handleScope;
		v8::Context::Scope contextScope(_contexts.front());

		evalAsValue(key + " = undefined", true);
		throw e;
	}
};

void V8DataModel::init(const std::string& location,
                       const Data& data) {
	try {
		assign(location, data);
	} catch (Event e) {
		// test 277
		v8::Locker locker;
		v8::HandleScope handleScope;
		v8::Context::Scope contextScope(_contexts.front());

		evalAsValue(location + " = undefined", true);
		throw e;
	}

}


v8::Handle<v8::Value> V8DataModel::evalAsValue(const std::string& expr, bool dontThrow) {
	v8::TryCatch tryCatch;
	v8::Handle<v8::String> source = v8::String::New(expr.c_str());
	v8::Handle<v8::Script> script = v8::Script::Compile(source);

	v8::Handle<v8::Value> result;
	if (!script.IsEmpty())
		result = script->Run();

	if (script.IsEmpty() || result.IsEmpty()) {
		// throw an exception
		if (tryCatch.HasCaught() && !dontThrow)
			throwExceptionEvent(tryCatch);
	}

	return result;
}

void V8DataModel::throwExceptionEvent(const v8::TryCatch& tryCatch) {
	assert(tryCatch.HasCaught());
	Event exceptionEvent;
	exceptionEvent.name = "error.execution";
	exceptionEvent.eventType = Event::PLATFORM;

	std::string exceptionString(*v8::String::AsciiValue(tryCatch.Exception()));
	exceptionEvent.data.compound["exception"] = Data(exceptionString, Data::VERBATIM);;

	v8::Handle<v8::Message> message = tryCatch.Message();
	if (!message.IsEmpty()) {
		std::string filename(*v8::String::AsciiValue(message->GetScriptResourceName()));
		exceptionEvent.data.compound["filename"] = Data(filename, Data::VERBATIM);

		std::string sourceLine(*v8::String::AsciiValue(message->GetSourceLine()));
		size_t startpos = sourceLine.find_first_not_of(" \t");
		if(std::string::npos != startpos) // removoe leading white space
			sourceLine = sourceLine.substr(startpos);

		exceptionEvent.data.compound["sourceline"] = Data(sourceLine, Data::VERBATIM);

		std::stringstream ssLineNumber;
		int lineNumber = message->GetLineNumber();
		ssLineNumber << lineNumber;
		exceptionEvent.data.compound["linenumber"] = Data(ssLineNumber.str());

		int startColumn = message->GetStartColumn();
		int endColumn = message->GetEndColumn();
		std::stringstream ssUnderline;
		for (int i = 0; i < startColumn; i++)
			ssUnderline << " ";
		for (int i = startColumn; i < endColumn; i++)
			ssUnderline << "^";
		exceptionEvent.data.compound["sourcemark"] = Data(ssUnderline.str(), Data::VERBATIM);

		std::string stackTrace(*v8::String::AsciiValue(tryCatch.StackTrace()));
		exceptionEvent.data.compound["stacktrace"] = Data(stackTrace, Data::VERBATIM);

	}

//	_interpreter->receiveInternal(exceptionEvent);
	throw(exceptionEvent);
}

}