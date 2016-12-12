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
#include "uscxml/util/URL.h"
#include "uscxml/util/String.h"

#include "V8DataModel.h"
//#include "V8SCXMLEvent.h"

#include "uscxml/messages/Event.h"
#include "uscxml/util/DOM.h"
#include "uscxml/interpreter/Logging.h"

#include <boost/algorithm/string.hpp>

using namespace XERCESC_NS;

static v8::Local<v8::Value> XMLString2JS(const XMLCh* input) {
	char* res = XERCESC_NS::XMLString::transcode(input);
	v8::Local<v8::Value> handle = v8::String::New(res);
	return handle;
}

static XMLCh* JS2XMLString(const v8::Local<v8::Value>& value) {
	v8::String::AsciiValue s(value);
	XMLCh* ret = XERCESC_NS::XMLString::transcode(*s);
	return(ret);
}

// this is the version we support here
#define SWIG_V8_VERSION 0x032317

#include "V8DOM.cpp.inc"

namespace uscxml {

V8DataModel::V8DataModel() {
//  _contexts.push_back(v8::Context::New());
}

V8DataModel::~V8DataModel() {
	_context.Dispose();
//    if (_isolate != NULL) {
//        _isolate->Dispose();
//    }
}

void V8DataModel::addExtension(DataModelExtension* ext) {
#if 0
	if (_extensions.find(ext) != _extensions.end())
		return;

	ext->dm = this;
	_extensions.insert(ext);

	v8::Locker locker;
	v8::HandleScope scope;
	v8::Context::Scope contextScope(_contexts.front());
	v8::Local<v8::Object> currScope = _contexts.front()->Global();

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
#endif
}

void V8DataModel::jsExtension(const v8::FunctionCallbackInfo<v8::Value>& info) {
#if 0
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
#endif
}

std::mutex V8DataModel::_initMutex;

v8::Isolate* V8DataModel::_isolate = NULL;

void V8NodeListIndexedPropertyHandler(uint32_t index, const v8::PropertyCallbackInfo<v8::Value>& info) {
	XERCESC_NS::DOMNodeList* list;
	SWIG_V8_GetInstancePtr(info.Holder(), (void**)&list);

	if (list->getLength() >= index) {
		XERCESC_NS::DOMNode* node = list->item(index);

		v8::Handle<v8::Value> val = SWIG_NewPointerObj(SWIG_as_voidptr(node), SWIG_TypeDynamicCast(SWIGTYPE_p_XERCES_CPP_NAMESPACE__DOMNode, SWIG_as_voidptrptr(&node)), 0 |  0 );
		info.GetReturnValue().Set(val);
		return;
	}
	info.GetReturnValue().Set(v8::Undefined());

}

std::shared_ptr<DataModelImpl> V8DataModel::create(DataModelCallbacks* callbacks) {
	std::shared_ptr<V8DataModel> dm(new V8DataModel());
	dm->_callbacks = callbacks;

	// TODO: we cannot use one isolate per thread as swig's type will be unknown :(
	// We could register them by hand and avoid the _export_ globals in swig?
	if (dm->_isolate == NULL) {
		dm->_isolate = v8::Isolate::New();
	}

	v8::Locker locker(dm->_isolate);
	v8::Isolate::Scope isoScope(dm->_isolate);

	// Create a handle scope to hold the temporary references.
	v8::HandleScope scope(dm->_isolate);

	// Create a template for the global object where we set the built-in global functions.
	v8::Local<v8::ObjectTemplate> global = v8::ObjectTemplate::New();

	// some free functions
	global->Set(v8::String::NewSymbol("print"),
	            v8::FunctionTemplate::New(dm->_isolate, jsPrint,v8::External::New(reinterpret_cast<void*>(dm.get()))));
	global->Set(v8::String::NewSymbol("In"),
	            v8::FunctionTemplate::New(dm->_isolate, jsIn, v8::External::New(reinterpret_cast<void*>(dm.get()))));

	v8::Local<v8::Context> context = v8::Context::New(dm->_isolate, NULL, global);

	dm->_context.Reset(dm->_isolate, context);

	// Enter the new context so all the following operations take place within it.
	v8::Context::Scope contextScope(context);
	assert(dm->_isolate->GetCurrentContext() == context);

	// not thread safe!
	{
		std::lock_guard<std::mutex> lock(_initMutex);
		SWIGV8_INIT(context->Global());

		// register subscript operator with nodelist
		v8::Handle<v8::FunctionTemplate> _exports_DOMNodeList_class = SWIGV8_CreateClassTemplate("_exports_DOMNodeList");

		_exports_DOMNodeList_class->InstanceTemplate()->SetIndexedPropertyHandler(V8NodeListIndexedPropertyHandler);
		SWIGV8_AddMemberFunction(_exports_DOMNodeList_class, "item", _wrap_DOMNodeList_item);
		SWIGV8_AddMemberFunction(_exports_DOMNodeList_class, "getLength", _wrap_DOMNodeList_getLength);

		SWIGV8_SET_CLASS_TEMPL(_exports_DOMNodeList_clientData.class_templ, _exports_DOMNodeList_class);

	}

	context->Global()->SetAccessor(v8::String::NewSymbol("_sessionid"),
	                               V8DataModel::getAttribute,
	                               V8DataModel::setWithException,
	                               v8::String::New(callbacks->getSessionId().c_str()));
	context->Global()->SetAccessor(v8::String::NewSymbol("_name"),
	                               V8DataModel::getAttribute,
	                               V8DataModel::setWithException,
	                               v8::String::New(callbacks->getName().c_str()));
	context->Global()->SetAccessor(v8::String::NewSymbol("_ioprocessors"),
	                               V8DataModel::getIOProcessors,
	                               V8DataModel::setWithException,
	                               v8::External::New(reinterpret_cast<void*>(dm.get())));
	context->Global()->SetAccessor(v8::String::NewSymbol("_invokers"),
	                               V8DataModel::getInvokers,
	                               V8DataModel::setWithException,
	                               v8::External::New(reinterpret_cast<void*>(dm.get())));

//    v8::Persistent<v8::Value, v8::CopyablePersistentTraits<v8::Value> > persistent(_isolate, context);

#if 0

	// instantiate the document function
	v8::Local<v8::Function> docCtor = V8Document::getTmpl()->GetFunction();
	v8::Local<v8::Object> docObj = docCtor->NewInstance();

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



	// instantiate objects - we have to have a context for that!
	dm->eval(Element<std::string>(), "_x = {};");
#endif

	return dm;
}

void V8DataModel::getAttribute(v8::Local<v8::String> property, const v8::PropertyCallbackInfo<v8::Value>& info) {
	info.GetReturnValue().Set(info.Data());
}

void V8DataModel::setWithException(v8::Local<v8::String> property,
                                   v8::Local<v8::Value> value,
                                   const v8::PropertyCallbackInfo<void>& info) {
	v8::String::AsciiValue data(property);
	std::string msg = "Cannot set " + std::string(*data);
	v8::ThrowException(v8::Exception::ReferenceError(v8::String::New(msg.c_str())));
}

void V8DataModel::getIOProcessors(v8::Local<v8::String> property, const v8::PropertyCallbackInfo<v8::Value>& info) {
	v8::Local<v8::External> field = v8::Local<v8::External>::Cast(info.Data());
	V8DataModel* dataModel = (V8DataModel*)field->Value();

	if (dataModel->_ioProcessors.IsEmpty()) {

		v8::Local<v8::Object> ioProcs = v8::Local<v8::Object>::New(v8::Isolate::GetCurrent(), v8::Object::New());
		//v8::Local<v8::Object> ioProcessorObj = v8::Object::New();
		std::map<std::string, IOProcessor> ioProcessors = dataModel->_callbacks->getIOProcessors();
		std::map<std::string, IOProcessor>::const_iterator ioProcIter = ioProcessors.begin();
		while(ioProcIter != ioProcessors.end()) {
			//			std::cout << ioProcIter->first << std::endl;
			ioProcs->Set(v8::String::New(ioProcIter->first.c_str()),
			             dataModel->getDataAsValue(ioProcIter->second.getDataModelVariables()));
			ioProcIter++;
		}
		dataModel->_ioProcessors.Reset(v8::Isolate::GetCurrent(), ioProcs);
	}
	info.GetReturnValue().Set(dataModel->_ioProcessors);
}

void V8DataModel::getInvokers(v8::Local<v8::String> property, const v8::PropertyCallbackInfo<v8::Value>& info) {
	v8::Local<v8::External> field = v8::Local<v8::External>::Cast(info.Data());
	V8DataModel* dataModel = (V8DataModel*)field->Value();

	if (dataModel->_invokers.IsEmpty()) {
		v8::Local<v8::Object> invoks = v8::Local<v8::Object>::New(v8::Isolate::GetCurrent(), v8::Object::New());
		//v8::Local<v8::Object> ioProcessorObj = v8::Object::New();
		std::map<std::string, Invoker> invokers = dataModel->_callbacks->getInvokers();
		std::map<std::string, Invoker>::const_iterator invokerIter = invokers.begin();
		while(invokerIter != invokers.end()) {
			//			std::cout << ioProcIter->first << std::endl;
			invoks->Set(v8::String::New(invokerIter->first.c_str()),
			            dataModel->getDataAsValue(invokerIter->second.getDataModelVariables()));
			invokerIter++;
		}
		dataModel->_invokers.Reset(v8::Isolate::GetCurrent(), invoks);

	}
	info.GetReturnValue().Set(dataModel->_invokers);
}

void V8DataModel::setEvent(const Event& event) {

	v8::Locker locker(_isolate);
	v8::Isolate::Scope isoScope(_isolate);

	v8::HandleScope scope(_isolate);
	v8::Local<v8::Context> ctx = v8::Local<v8::Context>::New(_isolate, _context);

	v8::Local<v8::Object> global = ctx->Global();
	v8::Context::Scope contextScope(ctx); // segfaults at newinstance without!
	assert(_isolate->GetCurrentContext() == ctx); // only valid in context::scope


#if 0
	// this would work as swig_exports_ will get redefined per isolate
	{
		std::lock_guard<std::mutex> lock(_initMutex);
		SWIGV8_INIT(context->Global());
	}
#endif

	Event* evPtr = new Event(event);

//    v8::Handle<v8::FunctionTemplate> classTmpl = v8::Local<v8::FunctionTemplate>::New(_isolate, V8SCXMLEvent::getTmpl());
//    v8::Local<v8::Object> eventObj = classTmpl->InstanceTemplate()->NewInstance();
//    eventObj->SetAlignedPointerInInternalField(0, (void*)evPtr);
//    assert(eventObj->GetAlignedPointerFromInternalField(0) == evPtr);

	v8::Local<v8::Value> eventVal = SWIG_V8_NewPointerObj(evPtr, SWIGTYPE_p_uscxml__Event, SWIG_POINTER_OWN);
	v8::Local<v8::Object> eventObj = v8::Local<v8::Object>::Cast(eventVal);

	/*
	    v8::Local<v8::Array> properties = eventObj->GetPropertyNames();
	    for (int i = 0; i < properties->Length(); i++) {
	        assert(properties->Get(i)->IsString());
	        v8::String::AsciiValue key(v8::Local<v8::String>::Cast(properties->Get(i)));
	        std::cout << *key << std::endl;
	    }
	*/

	// test333
	if (event.origintype.size() > 0) {
		eventObj->Set(v8::String::NewSymbol("origintype"),v8::String::NewFromUtf8(_isolate, event.origintype.c_str()));
	} else {
		eventObj->Set(v8::String::NewSymbol("origintype"),v8::Undefined(_isolate));
	}
	// test335
	if (event.origin.size() > 0) {
		eventObj->Set(v8::String::NewSymbol("origin"),v8::String::NewFromUtf8(_isolate, event.origin.c_str()));
	} else {
		eventObj->Set(v8::String::NewSymbol("origin"),v8::Undefined(_isolate));
	}
	// test337
	if (!event.hideSendId) {
		eventObj->Set(v8::String::NewSymbol("sendid"),v8::String::NewFromUtf8(_isolate, event.sendid.c_str()));
	} else {
		eventObj->Set(v8::String::NewSymbol("sendid"),v8::Undefined(_isolate));
	}
	// test339
	if (event.invokeid.size() > 0) {
		eventObj->Set(v8::String::NewSymbol("invokeid"),v8::String::NewFromUtf8(_isolate, event.invokeid.c_str()));
	} else {
		eventObj->Set(v8::String::NewSymbol("invokeid"),v8::Undefined(_isolate));
	}

	// test 331
	switch (event.eventType) {
	case Event::EXTERNAL:
		eventObj->Set(v8::String::NewSymbol("type"), v8::String::NewFromUtf8(_isolate, "external"));
		break;
	case Event::INTERNAL:
		eventObj->Set(v8::String::NewSymbol("type"), v8::String::NewFromUtf8(_isolate, "internal"));
		break;
	case Event::PLATFORM:
		eventObj->Set(v8::String::NewSymbol("type"), v8::String::NewFromUtf8(_isolate, "platform"));
		break;
	}

	if (event.data.node) {
		eventObj->Set(v8::String::NewSymbol("data"), getNodeAsValue(event.data.node));
	} else {
		// _event.data is KVP
		Data data = event.data;
		if (!event.params.empty()) {
			Event::params_t::const_iterator paramIter = event.params.begin();
			while(paramIter != event.params.end()) {
				data.compound[paramIter->first] = paramIter->second;
				paramIter++;
			}
		}
		if (!event.namelist.empty()) {
			Event::namelist_t::const_iterator nameListIter = event.namelist.begin();
			while(nameListIter != event.namelist.end()) {
				data.compound[nameListIter->first] = nameListIter->second;
				nameListIter++;
			}
		}
		if (!data.empty()) {
//			std::cout << Data::toJSON(eventCopy.data);
			eventObj->Set(v8::String::NewSymbol("data"), getDataAsValue(data)); // set data part of _event
		} else {
			// test 343 / test 488
			eventObj->Set(v8::String::NewSymbol("data"), v8::Undefined()); // set data part of _event
		}
	}
	// we cannot make _event v8::ReadOnly as it will ignore subsequent setEvents
	global->Set(v8::String::NewSymbol("_event"), eventObj);

//    _event.Reset(_isolate, eventObj);
//    _event = eventObj;
}

Data V8DataModel::getAsData(const std::string& content) {
	Data d = Data::fromJSON(content);
	if (!d.empty())
		return d;

	std::string trimmed = boost::trim_copy(content);
	if (trimmed.length() > 0) {
		if (isNumeric(trimmed.c_str(), 10)) {
			d = Data(trimmed, Data::INTERPRETED);
		} else if (trimmed.length() >= 2 &&
		           ((trimmed[0] == '"' && trimmed[trimmed.length() - 1] == '"') ||
		            (trimmed[0] == '\'' && trimmed[trimmed.length() - 1] == '\''))) {
			d = Data(trimmed.substr(1, trimmed.length() - 2), Data::VERBATIM);
		} else {
			d = Data(trimmed, Data::INTERPRETED);
		}
	}
	return d;
}

Data V8DataModel::evalAsData(const std::string& content) {
	v8::Locker locker(_isolate);
	v8::Isolate::Scope isoScope(_isolate);

	v8::HandleScope scope(_isolate);
	v8::Local<v8::Context> ctx = v8::Local<v8::Context>::New(_isolate, _context);
	v8::Context::Scope contextScope(ctx); // segfaults at newinstance without!

	v8::Local<v8::Value> result = evalAsValue(content);
	Data data = getValueAsData(result);
	return data;
}

Data V8DataModel::getValueAsData(const v8::Local<v8::Value>& value) {
	v8::Locker locker(_isolate);
	v8::Isolate::Scope isoScope(_isolate);
	v8::HandleScope scope(_isolate);

	std::set<v8::Value*> foo = std::set<v8::Value*>();
	return getValueAsData(value, foo);
}

Data V8DataModel::getValueAsData(const v8::Local<v8::Value>& value, std::set<v8::Value*>& alreadySeen) {

	v8::Local<v8::Context> ctx = v8::Local<v8::Context>::New(_isolate, _context);
	v8::Context::Scope contextScope(ctx); // segfaults at newinstance without!

	Data data;

	/// TODO: Breaking cycles does not work yet
	if (alreadySeen.find(*value) != alreadySeen.end())
		return data;
	alreadySeen.insert(*value);

	if (false) {
	} else if (value->IsArray()) {
		v8::Local<v8::Array> array = v8::Local<v8::Array>::Cast(value);
		for (int i = 0; i < array->Length(); i++) {
			data.array.push_back(getValueAsData(array->Get(i), alreadySeen));
		}
	} else if (value->IsBoolean()) {
		data.atom = (value->ToBoolean()->Value() ? "true" : "false");
	} else if (value->IsBooleanObject()) {
		LOG(_callbacks->getLogger(), USCXML_ERROR) << "IsBooleanObject is unimplemented" << std::endl;
	} else if (value->IsDate()) {
		LOG(_callbacks->getLogger(), USCXML_ERROR) << "IsDate is unimplemented" << std::endl;
	} else if (value->IsExternal()) {
		LOG(_callbacks->getLogger(), USCXML_ERROR) << "IsExternal is unimplemented" << std::endl;
	} else if (value->IsFalse()) {
		LOG(_callbacks->getLogger(), USCXML_ERROR) << "IsFalse is unimplemented" << std::endl;
	} else if (value->IsFunction()) {
		LOG(_callbacks->getLogger(), USCXML_ERROR) << "IsFunction is unimplemented" << std::endl;
	} else if (value->IsInt32()) {
		int32_t prop = value->Int32Value();
		data.atom = toStr(prop);
	} else if (value->IsNativeError()) {
		LOG(_callbacks->getLogger(), USCXML_ERROR) << "IsNativeError is unimplemented" << std::endl;
	} else if (value->IsNull()) {
		LOG(_callbacks->getLogger(), USCXML_ERROR) << "IsNull is unimplemented" << std::endl;
	} else if (value->IsNumber()) {
		v8::String::AsciiValue prop(v8::Local<v8::String>::Cast(v8::Local<v8::Number>::Cast(value)));
		data.atom = *prop;
	} else if (value->IsNumberObject()) {
		LOG(_callbacks->getLogger(), USCXML_ERROR) << "IsNumberObject is unimplemented" << std::endl;
	} else if (value->IsObject()) {

//		if (V8ArrayBuffer::hasInstance(value)) {
//			uscxml::V8ArrayBuffer::V8ArrayBufferPrivate* privObj = V8DOM::toClassPtr<V8ArrayBuffer::V8ArrayBufferPrivate >(value->ToObject()->GetInternalField(0));
//			data.binary = privObj->nativeObj->_blob;
//			return data;
//		}

		v8::Local<v8::FunctionTemplate> tmpl = v8::Local<v8::FunctionTemplate>::New(_isolate, _exports_DOMNode_clientData.class_templ);
		if (tmpl->HasInstance(value)) {
			SWIG_V8_GetInstancePtr(value, (void**)&(data.node));
			return data;
		}

		v8::Local<v8::Object> object = v8::Local<v8::Object>::Cast(value);
		v8::Local<v8::Array> properties = object->GetPropertyNames();
		for (int i = 0; i < properties->Length(); i++) {
			assert(properties->Get(i)->IsString());
			v8::String::AsciiValue key(v8::Local<v8::String>::Cast(properties->Get(i)));
			v8::Local<v8::Value> property = object->Get(properties->Get(i));
			data.compound[*key] = getValueAsData(property, alreadySeen);
		}
	} else if (value->IsRegExp()) {
		LOG(_callbacks->getLogger(), USCXML_ERROR) << "IsRegExp is unimplemented" << std::endl;
	} else if(value->IsString()) {
		v8::String::AsciiValue property(v8::Local<v8::String>::Cast(value));
		data.atom = *property;
		data.type = Data::VERBATIM;
	} else if(value->IsStringObject()) {
		LOG(_callbacks->getLogger(), USCXML_ERROR) << "IsStringObject is unimplemented" << std::endl;
	} else if(value->IsTrue()) {
		LOG(_callbacks->getLogger(), USCXML_ERROR) << "IsTrue is unimplemented" << std::endl;
	} else if(value->IsUint32()) {
		LOG(_callbacks->getLogger(), USCXML_ERROR) << "IsUint32 is unimplemented" << std::endl;
	} else if(value->IsUndefined()) {
		data.atom = "undefined";
	} else {
		LOG(_callbacks->getLogger(), USCXML_ERROR) << "Value's type is unknown!" << std::endl;
	}
	return data;
}

v8::Local<v8::Value> V8DataModel::getNodeAsValue(const XERCESC_NS::DOMNode* node) {
	return SWIG_NewPointerObj(SWIG_as_voidptr(node),
	                          SWIG_TypeDynamicCast(SWIGTYPE_p_XERCES_CPP_NAMESPACE__DOMNode,
	                                  SWIG_as_voidptrptr(&node)),
	                          0);
}

v8::Local<v8::Value> V8DataModel::getDataAsValue(const Data& data) {

	if (data.compound.size() > 0) {
		v8::Local<v8::Object> value = v8::Object::New();
		std::map<std::string, Data>::const_iterator compoundIter = data.compound.begin();
		while(compoundIter != data.compound.end()) {
			value->Set(v8::String::NewSymbol(compoundIter->first.c_str()), getDataAsValue(compoundIter->second));
			compoundIter++;
		}
		return value;
	}
	if (data.array.size() > 0) {
		v8::Local<v8::Object> value = v8::Array::New(_isolate, data.array.size());
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
	if (data.node) {
		return getNodeAsValue(data.node);
	}

//	if (data.binary) {
//		uscxml::ArrayBuffer* arrBuffer = new uscxml::ArrayBuffer(data.binary);
//		v8::Local<v8::Function> retCtor = V8ArrayBuffer::getTmpl()->GetFunction();
//		v8::Persistent<v8::Object> retObj = v8::Persistent<v8::Object>::New(retCtor->NewInstance());
//
//		struct V8ArrayBuffer::V8ArrayBufferPrivate* retPrivData = new V8ArrayBuffer::V8ArrayBufferPrivate();
//		retPrivData->nativeObj = arrBuffer;
//		retObj->SetInternalField(0, V8DOM::toExternal(retPrivData));
//
//		retObj.MakeWeak(0, V8ArrayBuffer::jsDestructor);
//		return retObj;
//	}
	// this will never be reached
	return v8::Undefined();
}

void V8DataModel::jsPrint(const v8::FunctionCallbackInfo<v8::Value>& info) {
	if (info.Length() > 0) {
		v8::String::AsciiValue printMsg(info[0]->ToString());
		std::cout << *printMsg;
	}
}

void V8DataModel::jsIn(const v8::FunctionCallbackInfo<v8::Value>& info) {
	v8::Local<v8::External> field = v8::Local<v8::External>::Cast(info.Data());
	V8DataModel* dataModel = (V8DataModel*)field->Value();

	for (unsigned int i = 0; i < info.Length(); i++) {
		if (info[i]->IsString()) {
			std::string stateName(*v8::String::AsciiValue(info[i]->ToString()));
			if (dataModel->_callbacks->isInState(stateName)) {
				continue;
			}
		}
		info.GetReturnValue().Set(false);
		return;
	}
	info.GetReturnValue().Set(true);
}

bool V8DataModel::isValidSyntax(const std::string& expr) {
	v8::TryCatch tryCatch;

	v8::Local<v8::String> source = v8::String::New(expr.c_str());
	v8::Local<v8::Script> script = v8::Script::Compile(source);

	if (script.IsEmpty() || tryCatch.HasCaught()) {
		return false;
	}

	return true;
}

uint32_t V8DataModel::getLength(const std::string& expr) {
	v8::Locker locker(_isolate);
	v8::Isolate::Scope isoScope(_isolate);
	v8::HandleScope scope(_isolate);

	v8::Local<v8::Context> ctx = v8::Local<v8::Context>::New(_isolate, _context);
	v8::Context::Scope contextScope(ctx); // segfaults at newinstance without!

	v8::Local<v8::Value> result = evalAsValue(expr);
	if (!result.IsEmpty() && result->IsArray())
		return result.As<v8::Array>()->Length();

	ERROR_EXECUTION_THROW("'" + expr + "' does not evaluate to an array.")
}

void V8DataModel::setForeach(const std::string& item,
                             const std::string& array,
                             const std::string& index,
                             uint32_t iteration) {
	if (!isDeclared(item)) {
		assign(item, Data());
	}

	v8::Locker locker(_isolate);
	v8::Isolate::Scope isoScope(_isolate);
	v8::HandleScope scope(_isolate);

	v8::Local<v8::Context> ctx = v8::Local<v8::Context>::New(_isolate, _context);
	v8::Context::Scope contextScope(ctx); // segfaults at newinstance without!

	// assign array element to item
	std::stringstream ss;
	ss << item << " = " << array << "[" << iteration << "]";
//	assign(item, Data(ss.str(), Data::INTERPRETED));
	// test152: we need "'continue' = array[index]" to throw
	evalAsValue(ss.str());
	if (index.length() > 0) {
		// assign iteration element to index
		std::stringstream ss;
		ss << iteration;
		assign(index, Data(ss.str(), Data::INTERPRETED));
	}
}

bool V8DataModel::isDeclared(const std::string& expr) {
	/**
	 * Undeclared variables can be checked by trying to access them and catching
	 * a reference error.
	 */

	v8::Locker locker(_isolate);
	v8::Isolate::Scope isoScope(_isolate);

	v8::HandleScope scope(_isolate);
	v8::Local<v8::Context> ctx = v8::Local<v8::Context>::New(_isolate, _context);
	v8::Context::Scope contextScope(ctx); // segfaults at newinstance without!

	v8::Local<v8::String> source = v8::String::New(expr.c_str());
	v8::Local<v8::Script> script = v8::Script::Compile(source);

	v8::Local<v8::Value> result;
	if (!script.IsEmpty())
		result = script->Run();

	if (result.IsEmpty())
		return false;

	return true;
}

bool V8DataModel::evalAsBool(const std::string& expr) {
	v8::Locker locker(_isolate);
	v8::Isolate::Scope isoScope(_isolate);

	v8::HandleScope scope(_isolate);
	v8::Local<v8::Context> ctx = v8::Local<v8::Context>::New(_isolate, _context);
	v8::Context::Scope contextScope(ctx); // segfaults at newinstance without!

	v8::Local<v8::Value> result = evalAsValue(expr);
	return(result->ToBoolean()->BooleanValue());
}


void V8DataModel::assign(const std::string& location, const Data& data) {

	v8::Locker locker(_isolate);
	v8::Isolate::Scope isoScope(_isolate);
	v8::HandleScope scope(_isolate);

	v8::Local<v8::Context> ctx = v8::Local<v8::Context>::New(_isolate, _context);
	v8::Local<v8::Object> global = ctx->Global();
	v8::Context::Scope contextScope(ctx); // segfaults at newinstance without!

	if (location.compare("_sessionid") == 0) // test 322
		ERROR_EXECUTION_THROW("Cannot assign to _sessionId");
	if (location.compare("_name") == 0)
		ERROR_EXECUTION_THROW("Cannot assign to _name");
	if (location.compare("_ioprocessors") == 0)  // test 326
		ERROR_EXECUTION_THROW("Cannot assign to _ioprocessors");
	if (location.compare("_invokers") == 0)
		ERROR_EXECUTION_THROW("Cannot assign to _invokers");
	if (location.compare("_event") == 0)
		ERROR_EXECUTION_THROW("Cannot assign to _event");

	if (data.node) {
		global->Set(v8::String::NewSymbol(location.c_str()), getNodeAsValue(data.node));
	} else {
		evalAsValue(location + " = " + Data::toJSON(data));
	}
}

void V8DataModel::init(const std::string& location,
                       const Data& data) {
	v8::Locker locker(_isolate);
	v8::Isolate::Scope isoScope(_isolate);
	v8::HandleScope scope(_isolate);

	v8::Local<v8::Context> ctx = v8::Local<v8::Context>::New(_isolate, _context);
	v8::Context::Scope contextScope(ctx); // segfaults at newinstance without!

	try {
		assign(location, data);
	} catch (ErrorEvent e) {
		// test 277
		evalAsValue(location + " = undefined", true);

		// we need to get error.execution into the queue
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

v8::Local<v8::Value> V8DataModel::evalAsValue(const std::string& expr, bool dontThrow) {

//    v8::Locker locker(_isolate);
//    v8::Isolate::Scope isoScope(_isolate);
//
//    v8::HandleScope scope(_isolate);
//    v8::EscapableHandleScope escape(_isolate);
//    v8::Local<v8::Context> ctx = v8::Local<v8::Context>::New(_isolate, _context);
//    v8::Context::Scope contextScope(ctx); // segfaults at newinstance without!

	v8::TryCatch tryCatch;

	v8::Local<v8::String> source = v8::String::New(expr.c_str());
	v8::Local<v8::Script> script = v8::Script::Compile(source);

	v8::Local<v8::Value> result;
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
	ErrorEvent exceptionEvent;
	exceptionEvent.name = "error.execution";
	exceptionEvent.eventType = Event::PLATFORM;

	std::string exceptionString(*v8::String::AsciiValue(tryCatch.Exception()));
	exceptionEvent.data.compound["cause"] = Data(exceptionString, Data::VERBATIM);;

	v8::Local<v8::Message> message = tryCatch.Message();
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
