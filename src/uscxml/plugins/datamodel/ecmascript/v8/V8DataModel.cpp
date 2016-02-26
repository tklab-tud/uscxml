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

/*
 * Later v8 changed API considerably, have a look at the node.js(!) documentatio for an overview:
 * http://strongloop.com/strongblog/node-js-v0-12-c-apis-breaking/
 */

#include "uscxml/Common.h"
#include "uscxml/config.h"
#include "V8DataModel.h"
#include "V8DOM.h"
#include "dom/V8Document.h"
#include "dom/V8Node.h"
#include "dom/V8Element.h"
#include "dom/V8Text.h"
#include "dom/V8CDATASection.h"
#include "dom/V8SCXMLEvent.h"

#include "dom/V8ArrayBuffer.h"
#include "dom/V8Int8Array.h"
#include "dom/V8Uint8Array.h"
#include "dom/V8Uint8ClampedArray.h"
#include "dom/V8Int16Array.h"
#include "dom/V8Uint16Array.h"
#include "dom/V8Int32Array.h"
#include "dom/V8Uint32Array.h"
#include "dom/V8Float32Array.h"
#include "dom/V8Float64Array.h"
#include "dom/V8DataView.h"

#include "uscxml/Message.h"
#include "uscxml/dom/DOMUtils.h"
#include <glog/logging.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

#define TO_V8_DOMVALUE(type) \
v8::Handle<v8::Function> retCtor = V8##type::getTmpl()->GetFunction();\
v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());\
struct V8##type::V8##type##Private* retPrivData = new V8##type::V8##type##Private();\
retPrivData->dom = _dom;\
retPrivData->nativeObj = new type<std::string>(node);\
retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));\
retObj.MakeWeak(0, V8##type::jsDestructor);\
return retObj;


namespace uscxml {

using namespace Arabica::XPath;
using namespace Arabica::DOM;

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool pluginConnect(pluma::Host& host) {
	host.add( new V8DataModelProvider() );
	return true;
}
#endif

V8DataModel::V8DataModel() : _ioProcessorsAreSet(false), _invokersAreSet(false) {
//  _contexts.push_back(v8::Context::New());
}

V8DataModel::~V8DataModel() {
	while(_contexts.size() > 0) {
		_contexts.back().Dispose();
		_contexts.pop_back();
	}
	if (_dom)
		delete _dom;
}

void V8DataModel::addExtension(DataModelExtension* ext) {
	if (_extensions.find(ext) != _extensions.end())
		return;

	ext->dm = this;
	_extensions.insert(ext);

	v8::Locker locker;
	v8::HandleScope scope;
	v8::Context::Scope contextScope(_contexts.front());
	v8::Handle<v8::Object> currScope = _contexts.front()->Global();

	std::list<std::string> locPath = tokenize(ext->provides(), '.');
	std::list<std::string>::iterator locIter = locPath.begin();
	while(true) {
		std::string pathComp = *locIter;
		v8::Local<v8::String> pathCompJS = v8::String::New(locIter->c_str());

		if (++locIter != locPath.end()) {
			// just another intermediate step
			if (!currScope->Has(pathCompJS)) {
				currScope->Set(pathCompJS, v8::Object::New());
			}

			v8::Local<v8::Value> newScope = currScope->Get(pathCompJS);
			if (newScope->IsObject()) {
				currScope = newScope->ToObject();
			} else {
				throw "Cannot add datamodel extension in non-object";
			}
		} else {
			// this is the function!
			currScope->Set(pathCompJS, v8::FunctionTemplate::New(jsExtension, v8::External::New(reinterpret_cast<void*>(ext)))->GetFunction(), v8::ReadOnly);
			break;
		}
	}
}

v8::Handle<v8::Value> V8DataModel::jsExtension(const v8::Arguments& args) {
	DataModelExtension* extension = static_cast<DataModelExtension*>(v8::External::Unwrap(args.Data()));

	v8::Local<v8::String> memberJS;
	std::string memberName;

	if (args.Length() > 0 && args[0]->IsString()) {
		memberJS = args[0]->ToString();
		memberName = *v8::String::AsciiValue(memberJS);
	}

	if (args.Length() > 1) {
		// setter
		Data data = ((V8DataModel*)(extension->dm))->getValueAsData(args[1]);
		extension->setValueOf(memberName, data);
		return v8::Undefined();
	}

	if (args.Length() == 1) {
		// getter
		return ((V8DataModel*)(extension->dm))->getDataAsValue(extension->getValueOf(memberName));
	}
	return v8::Undefined();
}

boost::shared_ptr<DataModelImpl> V8DataModel::create(InterpreterInfo* interpreter) {
	boost::shared_ptr<V8DataModel> dm = boost::shared_ptr<V8DataModel>(new V8DataModel());
	dm->_interpreter = interpreter;
	v8::Locker locker;
	v8::HandleScope scope;

	dm->_dom = new V8DOM();
//  dom->interpreter = interpreter;
	dm->_dom->xpath = new XPath<std::string>();
	dm->_dom->xpath->setNamespaceContext(*interpreter->getNameSpaceInfo().getNSContext());
	dm->_dom->storage	= new Storage(URL::getResourceDir() + PATH_SEPERATOR + interpreter->getName() + ".storage");
	dm->_dom->nsInfo = new NameSpaceInfo(interpreter->getNameSpaceInfo());
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

	// setup constructors
	context->Global()->Set(v8::String::New("ArrayBuffer"), V8ArrayBuffer::getConstructor()->GetFunction());
	context->Global()->Set(v8::String::New("Int8Array"), V8Int8Array::getConstructor()->GetFunction());
	context->Global()->Set(v8::String::New("Uint8Array"), V8Uint8Array::getConstructor()->GetFunction());
	context->Global()->Set(v8::String::New("Uint8ClampedArray"), V8Uint8ClampedArray::getConstructor()->GetFunction());
	context->Global()->Set(v8::String::New("Int16Array"), V8Int16Array::getConstructor()->GetFunction());
	context->Global()->Set(v8::String::New("Uint16Array"), V8Uint16Array::getConstructor()->GetFunction());
	context->Global()->Set(v8::String::New("Int32Array"), V8Int32Array::getConstructor()->GetFunction());
	context->Global()->Set(v8::String::New("Uint32Array"), V8Uint32Array::getConstructor()->GetFunction());
	context->Global()->Set(v8::String::New("Float32Array"), V8Float32Array::getConstructor()->GetFunction());
	context->Global()->Set(v8::String::New("Float64Array"), V8Float64Array::getConstructor()->GetFunction());
	context->Global()->Set(v8::String::New("DataView"), V8DataView::getConstructor()->GetFunction());


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
	context->Global()->SetAccessor(v8::String::New("_invokers"),
	                               V8DataModel::getInvokers,
	                               V8DataModel::setWithException,
	                               v8::External::New(reinterpret_cast<void*>(dm.get())));

	dm->_contexts.push_back(context);

	// instantiate objects - we have to have a context for that!
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

	if (!dataModel->_ioProcessorsAreSet) {
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
		dataModel->_ioProcessorsAreSet = true;
	}
	return dataModel->_ioProcessors;
}

v8::Handle<v8::Value> V8DataModel::getInvokers(v8::Local<v8::String> property, const v8::AccessorInfo& info) {
	V8DataModel* dataModel = V8DOM::toClassPtr<V8DataModel>(info.Data());

	if (!dataModel->_invokersAreSet) {
		dataModel->_invokers = v8::Persistent<v8::Object>::New(v8::Object::New());
		//v8::Handle<v8::Object> ioProcessorObj = v8::Object::New();
		std::map<std::string, Invoker> invokers = dataModel->_interpreter->getInvokers();
		std::map<std::string, Invoker>::const_iterator invokerIter = invokers.begin();
		while(invokerIter != invokers.end()) {
			//			std::cout << ioProcIter->first << std::endl;
			dataModel->_invokers->Set(v8::String::New(invokerIter->first.c_str()),
			                          dataModel->getDataAsValue(invokerIter->second.getDataModelVariables()));
			invokerIter++;
		}
		dataModel->_invokersAreSet = true;

	}
	return dataModel->_invokers;
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

	if (event.raw.size() == 0) {
		std::stringstream ssRaw;
		ssRaw << event;
		privData->nativeObj->raw = ssRaw.str();
	}

	if (event.dom) {
		eventObj->Set(v8::String::New("data"), getNodeAsValue(event.dom));
	} else if (event.content.length() > 0) {
		// _event.data is a string or JSON
		Data json = Data::fromJSON(event.content);
		if (!json.empty()) {
			eventObj->Set(v8::String::New("data"), getDataAsValue(json));
		} else {
			eventObj->Set(v8::String::New("data"), v8::String::New(spaceNormalize(event.content).c_str()));
		}
	} else {
		// _event.data is KVP
		Event eventCopy(event);
		if (!eventCopy.params.empty()) {
			Event::params_t::iterator paramIter = eventCopy.params.begin();
			while(paramIter != eventCopy.params.end()) {
				eventCopy.data.compound[paramIter->first] = paramIter->second;
				paramIter++;
			}
		}
		if (!eventCopy.namelist.empty()) {
			Event::namelist_t::iterator nameListIter = eventCopy.namelist.begin();
			while(nameListIter != eventCopy.namelist.end()) {
				eventCopy.data.compound[nameListIter->first] = nameListIter->second;
				nameListIter++;
			}
		}
		if (!eventCopy.data.empty()) {
//			std::cout << Data::toJSON(eventCopy.data);
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
		if (V8ArrayBuffer::hasInstance(value)) {
			uscxml::V8ArrayBuffer::V8ArrayBufferPrivate* privObj = V8DOM::toClassPtr<V8ArrayBuffer::V8ArrayBufferPrivate >(value->ToObject()->GetInternalField(0));
			data.binary = privObj->nativeObj->_blob;
			return data;
		}
		if (V8Node::hasInstance(value)) {
			uscxml::V8Node::V8NodePrivate* privObj = V8DOM::toClassPtr<V8Node::V8NodePrivate >(value->ToObject()->GetInternalField(0));
			data.node = *privObj->nativeObj;
			return data;
		}
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

v8::Handle<v8::Value> V8DataModel::getNodeAsValue(const Node<std::string>& node) {

	switch (node.getNodeType()) {
	case Node_base::ELEMENT_NODE:         {
		TO_V8_DOMVALUE(Element);
	}
	case Node_base::TEXT_NODE:            {
		TO_V8_DOMVALUE(Text);
	}
	case Node_base::CDATA_SECTION_NODE:   {
		TO_V8_DOMVALUE(CDATASection);
	}
	case Node_base::DOCUMENT_NODE:        {
		TO_V8_DOMVALUE(Document);
	}
	default:                              {
		TO_V8_DOMVALUE(Node);
	}
	}

}

v8::Handle<v8::Value> V8DataModel::getDataAsValue(const Data& data) {
	if (data.compound.size() > 0) {
		v8::Handle<v8::Object> value = v8::Object::New();
		std::map<std::string, Data>::const_iterator compoundIter = data.compound.begin();
		while(compoundIter != data.compound.end()) {
//			std::cout << compoundIter->first.c_str() << std::endl;
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
	if (data.atom.length() > 0) {
		switch (data.type) {
		case Data::VERBATIM:
			return v8::String::New(data.atom.c_str());
			break;
		case Data::INTERPRETED:
			return evalAsValue(data.atom);
			break;
		}
	}
	if (data.binary) {
		uscxml::ArrayBuffer* arrBuffer = new uscxml::ArrayBuffer(data.binary);
		v8::Handle<v8::Function> retCtor = V8ArrayBuffer::getTmpl()->GetFunction();
		v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());

		struct V8ArrayBuffer::V8ArrayBufferPrivate* retPrivData = new V8ArrayBuffer::V8ArrayBufferPrivate();
		retPrivData->nativeObj = arrBuffer;
		retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));

		retObj.MakeWeak(0, V8ArrayBuffer::jsDestructor);
		return retObj;
	}
	// this will never be reached
	return v8::Undefined();
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
			if (INSTANCE->_interpreter->isInState(stateName)) {
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

bool V8DataModel::isLocation(const std::string& expr) {
	// location needs to be RHS and ++ is only valid for RHS
	return isValidSyntax(expr + "++");
}

bool V8DataModel::isValidSyntax(const std::string& expr) {
	v8::Locker locker;
	v8::HandleScope handleScope;
	v8::TryCatch tryCatch;
	v8::Context::Scope contextScope(_contexts.back());

	v8::Handle<v8::String> source = v8::String::New(expr.c_str());
	v8::Handle<v8::Script> script = v8::Script::Compile(source);

	if (script.IsEmpty() || tryCatch.HasCaught()) {
		return false;
	}

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
	exceptionEvent.data.compound["cause"] = Data("'" + expr + "' does not evaluate to an array.", Data::VERBATIM);

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
	assign(item, Data(ss.str(), Data::INTERPRETED));
	if (index.length() > 0) {
		// assign iteration element to index
		std::stringstream ss;
		ss << iteration;
		assign(index, Data(ss.str(), Data::INTERPRETED));
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
	return evalAsBool(Arabica::DOM::Element<std::string>(), expr);
}

bool V8DataModel::evalAsBool(const Arabica::DOM::Element<std::string>& node, const std::string& expr) {
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
                         const Node<std::string>& node,
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

	if (key.compare("_sessionid") == 0) // test 322
		ERROR_EXECUTION_THROW("Cannot assign to _sessionId");
	if (key.compare("_name") == 0)
		ERROR_EXECUTION_THROW("Cannot assign to _name");
	if (key.compare("_ioprocessors") == 0)  // test 326
		ERROR_EXECUTION_THROW("Cannot assign to _ioprocessors");
	if (key.compare("_invokers") == 0)
		ERROR_EXECUTION_THROW("Cannot assign to _invokers");
	if (key.compare("_event") == 0)
		ERROR_EXECUTION_THROW("Cannot assign to _event");

	if (HAS_ATTR(assignElem, "expr")) {
		evalAsValue(key + " = " + ATTR(assignElem, "expr"));
	} else if (node) {
		global->Set(v8::String::New(key.c_str()), getNodeAsValue(node));
	} else if (content.size() > 0) {
		try {
			evalAsValue(key + " = " + content);
		} catch (...) {
			evalAsValue(key + " = " + "\"" + spaceNormalize(content) + "\"");
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
                       const Node<std::string>& doc,
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

std::string V8DataModel::andExpressions(std::list<std::string> expressions) {
	if (expressions.size() == 0)
		return "";

	if (expressions.size() == 1)
		return *(expressions.begin());

	std::ostringstream exprSS;
	exprSS << "(";
	std::string conjunction = "";
	for (std::list<std::string>::const_iterator exprIter = expressions.begin();
	        exprIter != expressions.end();
	        exprIter++) {
		exprSS << conjunction << "(" << *exprIter << ")";
		conjunction = " && ";
	}
	exprSS << ")";
	return exprSS.str();
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
	exceptionEvent.data.compound["cause"] = Data(exceptionString, Data::VERBATIM);;

	v8::Handle<v8::Message> message = tryCatch.Message();
	if (!message.IsEmpty()) {
		std::string filename(*v8::String::AsciiValue(message->GetScriptResourceName()));
		exceptionEvent.data.compound["filename"] = Data(filename, Data::VERBATIM);

		std::string sourceLine(*v8::String::AsciiValue(message->GetSourceLine()));
		size_t startpos = sourceLine.find_first_not_of(" \t");
		if(std::string::npos != startpos) // remove leading white space
			sourceLine = sourceLine.substr(startpos);

		exceptionEvent.data.compound["sourceline"] = Data(sourceLine, Data::VERBATIM);

		std::stringstream ssLineNumber;
		int lineNumber = message->GetLineNumber();
		ssLineNumber << lineNumber;
		exceptionEvent.data.compound["linenumber"] = Data(ssLineNumber.str(), Data::INTERPRETED);

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