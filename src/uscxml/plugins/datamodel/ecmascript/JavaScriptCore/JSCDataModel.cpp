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

#include "uscxml/Common.h"
#include "uscxml/config.h"
#include "JSCDataModel.h"
#include "JSCDOM.h"
#include "dom/JSCDocument.h"
#include "dom/JSCElement.h"
#include "dom/JSCText.h"
#include "dom/JSCCDATASection.h"
#include "dom/JSCSCXMLEvent.h"

#include "dom/JSCArrayBuffer.h"
#include "dom/JSCInt8Array.h"
#include "dom/JSCUint8Array.h"
#include "dom/JSCUint8ClampedArray.h"
#include "dom/JSCInt16Array.h"
#include "dom/JSCUint16Array.h"
#include "dom/JSCInt32Array.h"
#include "dom/JSCUint32Array.h"
#include "dom/JSCFloat32Array.h"
#include "dom/JSCFloat64Array.h"
#include "dom/JSCDataView.h"

#include "uscxml/Message.h"
#include "uscxml/DOMUtils.h"
#include <glog/logging.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

#define TO_JSC_DOMVALUE(type) \
struct JSC##type::JSC##type##Private* privData = new JSC##type::JSC##type##Private(); \
privData->dom = _dom; \
privData->nativeObj = new type<std::string>(node); \
JSObjectRef retObj = JSObjectMake(_ctx, JSC##type::getTmpl(), privData);\
return retObj;

#define JSC_ADD_GLOBAL_OBJECT(name, constructor)\
JSStringRef name##Name = JSStringCreateWithUTF8CString(#name);\
JSObjectRef name = JSObjectMake(dm->_ctx, constructor, NULL);\
JSObjectSetProperty(dm->_ctx, JSContextGetGlobalObject(dm->_ctx), name##Name, name, kJSPropertyAttributeReadOnly | kJSPropertyAttributeDontDelete, NULL);\
JSStringRelease(name##Name);

namespace uscxml {

using namespace Arabica::XPath;
using namespace Arabica::DOM;

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool pluginConnect(pluma::Host& host) {
	host.add( new JSCDataModelProvider() );
	return true;
}
#endif

JSCDataModel::JSCDataModel() {
	_dom = NULL;
	_ctx = NULL;
}

JSCDataModel::~JSCDataModel() {
	if (_dom)
		delete _dom;
	if (_ctx)
		JSGlobalContextRelease(_ctx);
}

void JSCDataModel::addExtension(DataModelExtension* ext) {
	if (_extensions.find(ext) != _extensions.end())
		return;
	
	ext->dm = this;
	_extensions.insert(ext);
	
	JSObjectRef currScope = JSContextGetGlobalObject(_ctx);
	std::list<std::string> locPath = InterpreterImpl::tokenize(ext->provides(), '.');
	std::list<std::string>::iterator locIter = locPath.begin();
	while(true) {
		std::string pathComp = *locIter;
		JSStringRef pathCompJS = JSStringCreateWithUTF8CString(pathComp.c_str());

		if (++locIter != locPath.end()) {
			// just another intermediate step
			if (!JSObjectHasProperty(_ctx, currScope, pathCompJS)) {
				JSObjectSetProperty(_ctx, currScope, pathCompJS, JSObjectMake(_ctx, NULL, NULL), kJSPropertyAttributeNone, NULL);
			}
			JSValueRef newScope = JSObjectGetProperty(_ctx, currScope, pathCompJS, NULL);
			JSStringRelease(pathCompJS);

			
			if (JSValueIsObject(_ctx, newScope)) {
				currScope = JSValueToObject(_ctx, newScope, NULL);
			} else {
				JSStringRelease(pathCompJS);
				throw "Cannot add datamodel extension in non-object";
			}
		} else {
			// this is the function!
			JSClassRef jsExtensionClassRef = JSClassCreate(&jsExtensionClassDef);
			JSObjectRef jsExtFuncObj = JSObjectMake(_ctx, jsExtensionClassRef, ext);
			JSObjectSetProperty(_ctx, currScope, pathCompJS, jsExtFuncObj, kJSPropertyAttributeNone, NULL);

			JSStringRelease(pathCompJS);
			break;
		}
	}
}

JSValueRef JSCDataModel::jsExtension(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObject, size_t argumentCount, const JSValueRef arguments[], JSValueRef* exception) {
	DataModelExtension* extension = (DataModelExtension*)JSObjectGetPrivate(function);
	
	JSStringRef memberRef;
	std::string memberName;
	
	if (argumentCount > 0 && JSValueIsString(ctx, arguments[0])) {
		memberRef = JSValueToStringCopy(ctx, arguments[0], exception);
		size_t maxSize = JSStringGetMaximumUTF8CStringSize(memberRef);
		char* buffer = new char[maxSize];
		JSStringGetUTF8CString(memberRef, buffer, maxSize);
		JSStringRelease(memberRef);
		memberName = buffer;
		free(buffer);
	}

	if (argumentCount > 1) {
		// setter
		Data data = ((JSCDataModel*)(extension->dm))->getValueAsData(arguments[1]);
		extension->setValueOf(memberName, data);
		return JSValueMakeNull(ctx);
	}
	if (argumentCount == 1) {
		// getter
		return ((JSCDataModel*)(extension->dm))->getDataAsValue(extension->getValueOf(memberName));
	}

	return JSValueMakeNull(ctx);
}

#if 0
typedef struct {
	int                                 version; /* current (and only) version is 0 */
	JSClassAttributes                   attributes;

	const char*                         className;
	JSClassRef                          parentClass;

	const JSStaticValue*                staticValues;
	const JSStaticFunction*             staticFunctions;

	JSObjectInitializeCallback          initialize;
	JSObjectFinalizeCallback            finalize;
	JSObjectHasPropertyCallback         hasProperty;
	JSObjectGetPropertyCallback         getProperty;
	JSObjectSetPropertyCallback         setProperty;
	JSObjectDeletePropertyCallback      deleteProperty;
	JSObjectGetPropertyNamesCallback    getPropertyNames;
	JSObjectCallAsFunctionCallback      callAsFunction;
	JSObjectCallAsConstructorCallback   callAsConstructor;
	JSObjectHasInstanceCallback         hasInstance;
	JSObjectConvertToTypeCallback       convertToType;
} JSClassDefinition;
#endif

// functions need to be objects to hold private data in JSC
JSClassDefinition JSCDataModel::jsInClassDef = { 0, 0, "In", 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, jsIn, 0, 0, 0 };
JSClassDefinition JSCDataModel::jsPrintClassDef = { 0, 0, "print", 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, jsPrint, 0, 0, 0 };
JSClassDefinition JSCDataModel::jsExtensionClassDef = { 0, 0, "Extension", 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, jsExtension, 0, 0, 0 };

JSClassDefinition JSCDataModel::jsIOProcessorsClassDef = { 0, 0, "ioProcessors", 0, 0, 0, 0, 0, jsIOProcessorHasProp, jsIOProcessorGetProp, 0, 0, jsIOProcessorListProps, 0, 0, 0, 0 };
JSClassDefinition JSCDataModel::jsInvokersClassDef = { 0, 0, "invokers", 0, 0, 0, 0, 0, jsInvokerHasProp, jsInvokerGetProp, 0, 0, jsInvokerListProps, 0, 0, 0, 0 };

boost::shared_ptr<DataModelImpl> JSCDataModel::create(InterpreterInfo* interpreter) {
	boost::shared_ptr<JSCDataModel> dm = boost::shared_ptr<JSCDataModel>(new JSCDataModel());

	dm->_ctx = JSGlobalContextCreate(NULL);
	dm->_interpreter = interpreter;

    dm->_dom = new JSCDOM();
    dm->_dom->xpath = new XPath<std::string>();
    dm->_dom->xpath->setNamespaceContext(*interpreter->getNameSpaceInfo().getNSContext());
    dm->_dom->storage	= new Storage(URL::getResourceDir() + PATH_SEPERATOR + interpreter->getName() + ".storage");
    dm->_dom->nsInfo	= new NameSpaceInfo(interpreter->getNameSpaceInfo());
    
	// introduce global functions as objects for private data
	JSClassRef jsInClassRef = JSClassCreate(&jsInClassDef);
	JSObjectRef jsIn = JSObjectMake(dm->_ctx, jsInClassRef, dm.get());
	JSStringRef inName = JSStringCreateWithUTF8CString("In");
	JSObjectSetProperty(dm->_ctx, JSContextGetGlobalObject(dm->_ctx), inName, jsIn, kJSPropertyAttributeNone, NULL);
	JSStringRelease(inName);

	JSClassRef jsPrintClassRef = JSClassCreate(&jsPrintClassDef);
	JSObjectRef jsPrint = JSObjectMake(dm->_ctx, jsPrintClassRef, dm.get());
	JSStringRef printName = JSStringCreateWithUTF8CString("print");
	JSObjectSetProperty(dm->_ctx, JSContextGetGlobalObject(dm->_ctx), printName, jsPrint, kJSPropertyAttributeNone, NULL);
	JSStringRelease(printName);

	JSClassRef jsInvokerClassRef = JSClassCreate(&jsInvokersClassDef);
	JSObjectRef jsInvoker = JSObjectMake(dm->_ctx, jsInvokerClassRef, dm.get());
	JSStringRef invokerName = JSStringCreateWithUTF8CString("_invokers");
	JSObjectSetProperty(dm->_ctx, JSContextGetGlobalObject(dm->_ctx), invokerName, jsInvoker, kJSPropertyAttributeReadOnly | kJSPropertyAttributeDontDelete, NULL);
	JSStringRelease(invokerName);

	JSClassRef jsIOProcClassRef = JSClassCreate(&jsIOProcessorsClassDef);
	JSObjectRef jsIOProc = JSObjectMake(dm->_ctx, jsIOProcClassRef, dm.get());
	JSStringRef ioProcName = JSStringCreateWithUTF8CString("_ioprocessors");
	JSObjectSetProperty(dm->_ctx, JSContextGetGlobalObject(dm->_ctx), ioProcName, jsIOProc, kJSPropertyAttributeReadOnly | kJSPropertyAttributeDontDelete, NULL);
	JSStringRelease(ioProcName);

	JSStringRef nameName = JSStringCreateWithUTF8CString("_name");
	JSStringRef name = JSStringCreateWithUTF8CString(dm->_interpreter->getName().c_str());
	JSObjectSetProperty(dm->_ctx, JSContextGetGlobalObject(dm->_ctx), nameName, JSValueMakeString(dm->_ctx, name), kJSPropertyAttributeReadOnly | kJSPropertyAttributeDontDelete, NULL);
	JSStringRelease(nameName);
	JSStringRelease(name);

	JSStringRef sessionIdName = JSStringCreateWithUTF8CString("_sessionid");
	JSStringRef sessionId = JSStringCreateWithUTF8CString(dm->_interpreter->getSessionId().c_str());
	JSObjectSetProperty(dm->_ctx, JSContextGetGlobalObject(dm->_ctx), sessionIdName, JSValueMakeString(dm->_ctx, sessionId), kJSPropertyAttributeReadOnly | kJSPropertyAttributeDontDelete, NULL);
	JSStringRelease(sessionIdName);
	JSStringRelease(sessionId);

	JSC_ADD_GLOBAL_OBJECT(ArrayBuffer, JSCArrayBuffer::getTmpl());
	JSC_ADD_GLOBAL_OBJECT(Int8Array, JSCInt8Array::getTmpl());
	JSC_ADD_GLOBAL_OBJECT(Uint8Array, JSCUint8Array::getTmpl());
	JSC_ADD_GLOBAL_OBJECT(Uint8ClampedArray, JSCUint8ClampedArray::getTmpl());
	JSC_ADD_GLOBAL_OBJECT(Int16Array, JSCInt16Array::getTmpl());
	JSC_ADD_GLOBAL_OBJECT(Uint16Array, JSCUint16Array::getTmpl());
	JSC_ADD_GLOBAL_OBJECT(Int32Array, JSCInt32Array::getTmpl());
	JSC_ADD_GLOBAL_OBJECT(Uint32Array, JSCUint32Array::getTmpl());
	JSC_ADD_GLOBAL_OBJECT(Float32Array, JSCFloat32Array::getTmpl());
	JSC_ADD_GLOBAL_OBJECT(Float64Array, JSCFloat64Array::getTmpl());
	JSC_ADD_GLOBAL_OBJECT(DataView, JSCDataView::getTmpl());

	JSCDocument::JSCDocumentPrivate* privData = new JSCDocument::JSCDocumentPrivate();
	if (interpreter) {
		privData->nativeObj = new Document<std::string>(interpreter->getDocument());
		privData->dom = dm->_dom;

		JSObjectRef documentObject = JSObjectMake(dm->_ctx, JSCDocument::getTmpl(), privData);
		JSObjectRef globalObject = JSContextGetGlobalObject(dm->_ctx);
		JSStringRef documentName = JSStringCreateWithUTF8CString("document");

		JSObjectSetProperty(dm->_ctx, globalObject, documentName, documentObject, kJSPropertyAttributeReadOnly | kJSPropertyAttributeDontDelete, NULL);
		JSStringRelease(documentName);
	}

	dm->eval(Element<std::string>(), "_x = {};");

	return dm;
}

void JSCDataModel::pushContext() {
}

void JSCDataModel::popContext() {
}

void JSCDataModel::setEvent(const Event& event) {
	JSCSCXMLEvent::JSCSCXMLEventPrivate* privData = new JSCSCXMLEvent::JSCSCXMLEventPrivate();
	privData->nativeObj = new Event(event);
	privData->dom = _dom;

	JSObjectRef eventObj = JSObjectMake(_ctx, JSCSCXMLEvent::getTmpl(), privData);
	JSObjectRef globalObject = JSContextGetGlobalObject(_ctx);

	JSValueRef exception = NULL;

	if (event.raw.size() == 0) {
		std::stringstream ssRaw;
		ssRaw << event;
		privData->nativeObj->raw = ssRaw.str();
	}

	if (event.dom) {
		JSStringRef propName = JSStringCreateWithUTF8CString("data");
		JSObjectSetProperty(_ctx, eventObj, propName, getNodeAsValue(event.dom), 0, &exception);
		JSStringRelease(propName);
		if (exception)
			handleException(exception);

	} else if (event.content.length() > 0) {
		// _event.data is a string or JSON
		Data json = Data::fromJSON(event.content);
		if (!json.empty()) {
			JSStringRef propName = JSStringCreateWithUTF8CString("data");
			JSObjectSetProperty(_ctx, eventObj, propName, getDataAsValue(json), 0, &exception);
			JSStringRelease(propName);
			if (exception)
				handleException(exception);
		} else {
			JSStringRef propName = JSStringCreateWithUTF8CString("data");
			JSStringRef contentStr = JSStringCreateWithUTF8CString(InterpreterImpl::spaceNormalize(event.content).c_str());
			JSObjectSetProperty(_ctx, eventObj, propName, JSValueMakeString(_ctx, contentStr), 0, &exception);
			JSStringRelease(propName);
			JSStringRelease(contentStr);

			if (exception)
				handleException(exception);
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
			JSStringRef propName = JSStringCreateWithUTF8CString("data");
			JSObjectSetProperty(_ctx, eventObj, propName, getDataAsValue(eventCopy.data), 0, &exception);
			JSStringRelease(propName);
			if (exception)
				handleException(exception);
		} else {
			// test 343 / test 488
			JSStringRef propName = JSStringCreateWithUTF8CString("data");
			JSObjectSetProperty(_ctx, eventObj, propName, JSValueMakeUndefined(_ctx), 0, &exception);
			JSStringRelease(propName);
			if (exception)
				handleException(exception);
		}
	}
	JSStringRef eventName = JSStringCreateWithUTF8CString("_event");
	JSObjectSetProperty(_ctx, globalObject, eventName, eventObj, kJSPropertyAttributeDontDelete, &exception);
	JSStringRelease(eventName);
	if (exception)
		handleException(exception);

}

Data JSCDataModel::getStringAsData(const std::string& content) {
	JSValueRef result = evalAsValue(content);
	Data data = getValueAsData(result);
	return data;
}

JSValueRef JSCDataModel::getDataAsValue(const Data& data) {
	JSValueRef exception = NULL;

	if (data.node) {
		JSCNode::JSCNodePrivate* privData = new JSCNode::JSCNodePrivate();
		privData->nativeObj = new Node<std::string>(data.node);
		privData->dom = _dom;

		JSObjectRef value = JSObjectMake(_ctx, JSCNode::getTmpl(), privData);
		return value;
	}
	if (data.compound.size() > 0) {
		JSObjectRef value = JSObjectMake(_ctx, 0, 0);
		std::map<std::string, Data>::const_iterator compoundIter = data.compound.begin();
		while(compoundIter != data.compound.end()) {
			JSStringRef key = JSStringCreateWithUTF8CString(compoundIter->first.c_str());
			JSObjectSetProperty(_ctx, value, key, getDataAsValue(compoundIter->second), 0, &exception);
			JSStringRelease(key);
			if (exception)
				handleException(exception);
			compoundIter++;
		}
		return value;
	}
	if (data.array.size() > 0) {
		JSValueRef elements[data.array.size()];
		std::list<Data>::const_iterator arrayIter = data.array.begin();
		uint32_t index = 0;
		while(arrayIter != data.array.end()) {
			elements[index++] = getDataAsValue(*arrayIter);
			arrayIter++;
		}
		JSObjectRef value = JSObjectMakeArray(_ctx, data.array.size(), elements, &exception);
		if (exception)
			handleException(exception);
		return value;
	}
	if (data.atom.size() > 0) {
		switch (data.type) {
		case Data::VERBATIM: {
			JSStringRef stringRef = JSStringCreateWithUTF8CString(data.atom.c_str());
			JSValueRef value = JSValueMakeString(_ctx, stringRef);
			JSStringRelease(stringRef);
			return value;
			break;
		}
		case Data::INTERPRETED: {
			return evalAsValue(data.atom);
			break;
		}
		}
	}
	if (data.binary) {
		uscxml::ArrayBuffer* localInstance = new uscxml::ArrayBuffer(data.binary);

		JSClassRef retClass = JSCArrayBuffer::getTmpl();
		struct JSCArrayBuffer::JSCArrayBufferPrivate* retPrivData = new JSCArrayBuffer::JSCArrayBufferPrivate();
		retPrivData->nativeObj = localInstance;

		JSObjectRef retObj = JSObjectMake(_ctx, retClass, retPrivData);
		return retObj;
	}
	return JSValueMakeUndefined(_ctx);
}

Data JSCDataModel::getValueAsData(const JSValueRef value) {
	Data data;
	JSValueRef exception = NULL;
	switch(JSValueGetType(_ctx, value)) {
	case kJSTypeUndefined:
	case kJSTypeNull:
		data.atom = "null";
		data.type = Data::INTERPRETED;
		break;
	case kJSTypeBoolean:
		data.atom = (JSValueToBoolean(_ctx, value) ? "true" : "false");
		break;
	case kJSTypeNumber:
		data.atom = toStr(JSValueToNumber(_ctx, value, &exception));
		if (exception)
			handleException(exception);
		break;
	case kJSTypeString: {
		JSStringRef stringValue = JSValueToStringCopy( _ctx, value, &exception);
		if (exception)
			handleException(exception);

		size_t maxSize = JSStringGetMaximumUTF8CStringSize(stringValue);
		char* buf = new char[maxSize];
		JSStringGetUTF8CString(stringValue, buf, maxSize);

		data.atom = std::string(buf);
		data.type = Data::VERBATIM;
		JSStringRelease(stringValue);
		free(buf);
		break;
	}
	case kJSTypeObject: {
		JSObjectRef objValue = JSValueToObject(_ctx, value, &exception);
		if (exception)
			handleException(exception);
		if (JSValueIsObjectOfClass(_ctx, value, JSCArrayBuffer::getTmpl())) {
			// binary data
			JSCArrayBuffer::JSCArrayBufferPrivate* privObj = (JSCArrayBuffer::JSCArrayBufferPrivate*)JSObjectGetPrivate(objValue);
			data.binary = privObj->nativeObj->_blob;
			return data;
		} else if (JSValueIsObjectOfClass(_ctx, value, JSCNode::getTmpl())) {
			// dom node
			JSCNode::JSCNodePrivate* privObj = (JSCNode::JSCNodePrivate*)JSObjectGetPrivate(objValue);
			data.node = *privObj->nativeObj;
			return data;
		}
		std::set<std::string> propertySet;

		JSPropertyNameArrayRef properties = JSObjectCopyPropertyNames(_ctx, objValue);
		size_t paramCount = JSPropertyNameArrayGetCount(properties);
		bool isArray = true;
		for (size_t i = 0; i < paramCount; i++) {
			JSStringRef stringValue = JSPropertyNameArrayGetNameAtIndex(properties, i);
			size_t maxSize = JSStringGetMaximumUTF8CStringSize(stringValue);
			char* buf = new char[maxSize];
			JSStringGetUTF8CString(stringValue, buf, maxSize);
			std::string property(buf);
			if (!isNumeric(property.c_str(), 10))
				isArray = false;
			propertySet.insert(property);
			//JSStringRelease(stringValue); // JSPropertyNameArrayRelease does the job it seems
			free(buf);
		}
		JSPropertyNameArrayRelease(properties);
		std::set<std::string>::iterator propIter = propertySet.begin();
		while(propIter != propertySet.end()) {
			if (isArray) {
				JSValueRef nestedValue = JSObjectGetPropertyAtIndex(_ctx, objValue, strTo<int>(*propIter), &exception);
				if (exception)
					handleException(exception);
				data.array.push_back(getValueAsData(nestedValue));
			} else {
				JSStringRef jsString = JSStringCreateWithUTF8CString(propIter->c_str());
				JSValueRef nestedValue = JSObjectGetProperty(_ctx, objValue, jsString, &exception);
				JSStringRelease(jsString);
				if (exception)
					handleException(exception);
				data.compound[*propIter] = getValueAsData(nestedValue);
			}
			propIter++;
		}
		break;
	}
	}
	return data;
}

bool JSCDataModel::validate(const std::string& location, const std::string& schema) {
	return true;
}

uint32_t JSCDataModel::getLength(const std::string& expr) {
	JSValueRef result;

	result = evalAsValue("(" + expr + ").length");
	JSType type = JSValueGetType(_ctx, result);
	if (type == kJSTypeNull || type == kJSTypeUndefined) {
		ERROR_EXECUTION_THROW("'" + expr + "' does not evaluate to an array.");
	}

	JSValueRef exception = NULL;
	double length = JSValueToNumber(_ctx, result, &exception);
	if (exception)
		handleException(exception);

	return (uint32_t)length;
}

void JSCDataModel::setForeach(const std::string& item,
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

bool JSCDataModel::isLocation(const std::string& expr) {
	// location needs to be LHS and ++ is only valid for LHS
	return isValidSyntax(expr + "++");
}

bool JSCDataModel::isValidSyntax(const std::string& expr) {
	JSStringRef scriptJS = JSStringCreateWithUTF8CString(expr.c_str());
	JSValueRef exception = NULL;
	bool valid = JSCheckScriptSyntax(_ctx, scriptJS, NULL, 0, &exception);
	JSStringRelease(scriptJS);

	if (exception || !valid) {
		return false;
	}
	return true;
}

bool JSCDataModel::isDeclared(const std::string& expr) {
	JSStringRef scriptJS = JSStringCreateWithUTF8CString(expr.c_str());
	JSValueRef exception = NULL;
	JSValueRef result = JSEvaluateScript(_ctx, scriptJS, NULL, NULL, 0, &exception);
	JSStringRelease(scriptJS);

	if (exception || JSValueIsNull(_ctx, result)) {
		return false;
	}
	return true;
}

void JSCDataModel::eval(const Element<std::string>& scriptElem,
                        const std::string& expr) {
	evalAsValue(expr);
}

bool JSCDataModel::evalAsBool(const Arabica::DOM::Element<std::string>& node, const std::string& expr) {
	JSValueRef result = evalAsValue(expr);
	return JSValueToBoolean(_ctx, result);
}

std::string JSCDataModel::evalAsString(const std::string& expr) {
	JSValueRef result = evalAsValue(expr);
	JSValueRef exception = NULL;

	JSStringRef stringValue = JSValueToStringCopy( _ctx, result, &exception);
	if (exception)
		handleException(exception);

	size_t maxSize = JSStringGetMaximumUTF8CStringSize(stringValue);
	char data[maxSize];
	JSStringGetUTF8CString(stringValue, data, maxSize);
	std::string retString(data);

	JSStringRelease(stringValue);

	return retString;
}

JSValueRef JSCDataModel::evalAsValue(const std::string& expr, bool dontThrow) {
	JSStringRef scriptJS = JSStringCreateWithUTF8CString(expr.c_str());
	JSValueRef exception = NULL;
	JSValueRef result = JSEvaluateScript(_ctx, scriptJS, NULL, NULL, 0, &exception);
	JSStringRelease(scriptJS);

	if (exception && !dontThrow)
		handleException(exception);

	return result;
}

void JSCDataModel::assign(const Element<std::string>& assignElem,
                          const Node<std::string>& node,
                          const std::string& content) {
	std::string key;
	JSValueRef exception = NULL;
	if (HAS_ATTR(assignElem, "id")) {
		key = ATTR(assignElem, "id");
	} else if (HAS_ATTR(assignElem, "location")) {
		key = ATTR(assignElem, "location");
	}
	if (key.length() == 0) {
		ERROR_EXECUTION_THROW("Assign element has neither id nor location");
	}
	// flags on attribute are ignored?
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
		JSObjectSetProperty(_ctx, JSContextGetGlobalObject(_ctx), JSStringCreateWithUTF8CString(key.c_str()), getNodeAsValue(node), 0, &exception);
		if (exception)
			handleException(exception);
	} else if (content.size() > 0) {
		try {
			evalAsValue(key + " = " + content);
		} catch (...) {
			evalAsValue(key + " = " + "\"" + InterpreterImpl::spaceNormalize(content) + "\"");
		}
	} else {
		JSObjectSetProperty(_ctx, JSContextGetGlobalObject(_ctx), JSStringCreateWithUTF8CString(key.c_str()), JSValueMakeUndefined(_ctx), 0, &exception);
		if (exception)
			handleException(exception);
	}
}

JSValueRef JSCDataModel::getNodeAsValue(const Node<std::string>& node) {
	switch (node.getNodeType()) {
	case Node_base::ELEMENT_NODE:         {
		TO_JSC_DOMVALUE(Element);
	}
	case Node_base::TEXT_NODE:            {
		TO_JSC_DOMVALUE(Text);
	}
	case Node_base::CDATA_SECTION_NODE:   {
		TO_JSC_DOMVALUE(CDATASection);
	}
	case Node_base::DOCUMENT_NODE:        {
		TO_JSC_DOMVALUE(Document);
	}
	default:                              {
		TO_JSC_DOMVALUE(Node);
	}
	}
}

void JSCDataModel::assign(const std::string& location, const Data& data) {
	std::stringstream ssJSON;
	ssJSON << data;
	evalAsValue(location + " = " + ssJSON.str());
}

void JSCDataModel::init(const Element<std::string>& dataElem,
                        const Node<std::string>& node,
                        const std::string& content) {
	try {
		assign(dataElem, node, content);
	} catch (Event e) {
		// test 277
		std::string key;
		if (HAS_ATTR(dataElem, "id")) {
			key = ATTR(dataElem, "id");
		} else if (HAS_ATTR(dataElem, "location")) {
			key = ATTR(dataElem, "location");
		}
		evalAsValue(key + " = undefined", true);
		throw e;
	}
}

void JSCDataModel::init(const std::string& location, const Data& data) {
	try {
		assign(location, data);
	} catch (Event e) {
		// test 277
		evalAsValue(location + " = undefined", true);
		throw e;
	}
}

std::string JSCDataModel::andExpressions(std::list<std::string> expressions) {

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

void JSCDataModel::handleException(JSValueRef exception) {
	JSStringRef exceptionStringRef = JSValueToStringCopy(_ctx, exception, NULL);
	size_t maxSize = JSStringGetMaximumUTF8CStringSize(exceptionStringRef);
	char buffer[maxSize];
	JSStringGetUTF8CString(exceptionStringRef, buffer, maxSize);
	JSStringRelease(exceptionStringRef);
	std::string exceptionMsg(buffer);

	ERROR_EXECUTION_THROW(exceptionMsg);
}

JSValueRef JSCDataModel::jsPrint(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObject, size_t argumentCount, const JSValueRef arguments[], JSValueRef* exception) {
	JSCDataModel* INSTANCE = (JSCDataModel*)JSObjectGetPrivate(function);

	for (unsigned int i = 0; i < argumentCount; i++) {
		if (JSValueIsString(ctx, arguments[i])) {
			JSStringRef stringRef = JSValueToStringCopy(ctx, arguments[i], exception);
			if (*exception)
				INSTANCE->handleException(*exception);

			size_t maxSize = JSStringGetMaximumUTF8CStringSize(stringRef);
			char* buffer = new char[maxSize];

			JSStringGetUTF8CString(stringRef, buffer, maxSize);
			JSStringRelease(stringRef);
			std::string msg(buffer);
			free(buffer);

			std::cout << msg;
		}
	}
	return JSValueMakeUndefined(ctx);
}

JSValueRef JSCDataModel::jsIn(JSContextRef ctx, JSObjectRef function, JSObjectRef thisObject, size_t argumentCount, const JSValueRef arguments[], JSValueRef* exception) {
	JSCDataModel* INSTANCE = (JSCDataModel*)JSObjectGetPrivate(function);

	for (unsigned int i = 0; i < argumentCount; i++) {
		if (JSValueIsString(ctx, arguments[i])) {
			JSStringRef stringRef = JSValueToStringCopy(ctx, arguments[i], exception);
			if (*exception)
				INSTANCE->handleException(*exception);

			size_t maxSize = JSStringGetMaximumUTF8CStringSize(stringRef);
			char* buffer = new char[maxSize];

			JSStringGetUTF8CString(stringRef, buffer, maxSize);
			JSStringRelease(stringRef);
			std::string stateName(buffer);
			free(buffer);

			if (INSTANCE->_interpreter->isInState(stateName)) {
				continue;
			}
		}
		return JSValueMakeBoolean(ctx, false);
	}
	return JSValueMakeBoolean(ctx, true);

}

bool JSCDataModel::jsIOProcessorHasProp(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName) {
	JSCDataModel* INSTANCE = (JSCDataModel*)JSObjectGetPrivate(object);
	std::map<std::string, IOProcessor> ioProcessors = INSTANCE->_interpreter->getIOProcessors();

	size_t maxSize = JSStringGetMaximumUTF8CStringSize(propertyName);
	char buffer[maxSize];
	JSStringGetUTF8CString(propertyName, buffer, maxSize);
	std::string prop(buffer);

	return ioProcessors.find(prop) != ioProcessors.end();
}

JSValueRef JSCDataModel::jsIOProcessorGetProp(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef* exception) {
	JSCDataModel* INSTANCE = (JSCDataModel*)JSObjectGetPrivate(object);
	std::map<std::string, IOProcessor> ioProcessors = INSTANCE->_interpreter->getIOProcessors();

	size_t maxSize = JSStringGetMaximumUTF8CStringSize(propertyName);
	char buffer[maxSize];
	JSStringGetUTF8CString(propertyName, buffer, maxSize);
	std::string prop(buffer);

	if (ioProcessors.find(prop) != ioProcessors.end()) {
		return INSTANCE->getDataAsValue(ioProcessors.find(prop)->second.getDataModelVariables());
	}
	return JSValueMakeUndefined(ctx);
}

void JSCDataModel::jsIOProcessorListProps(JSContextRef ctx, JSObjectRef object, JSPropertyNameAccumulatorRef propertyNames) {
	JSCDataModel* INSTANCE = (JSCDataModel*)JSObjectGetPrivate(object);
	std::map<std::string, IOProcessor> ioProcessors = INSTANCE->_interpreter->getIOProcessors();

	std::map<std::string, IOProcessor>::const_iterator ioProcIter = ioProcessors.begin();
	while(ioProcIter != ioProcessors.end()) {
		JSStringRef ioProcName = JSStringCreateWithUTF8CString(ioProcIter->first.c_str());
		JSPropertyNameAccumulatorAddName(propertyNames, ioProcName);
		ioProcIter++;
	}
}


bool JSCDataModel::jsInvokerHasProp(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName) {
	JSCDataModel* INSTANCE = (JSCDataModel*)JSObjectGetPrivate(object);
	std::map<std::string, Invoker> invokers = INSTANCE->_interpreter->getInvokers();

	size_t maxSize = JSStringGetMaximumUTF8CStringSize(propertyName);
	char buffer[maxSize];
	JSStringGetUTF8CString(propertyName, buffer, maxSize);
	std::string prop(buffer);

	return invokers.find(prop) != invokers.end();
}

JSValueRef JSCDataModel::jsInvokerGetProp(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef* exception) {
	JSCDataModel* INSTANCE = (JSCDataModel*)JSObjectGetPrivate(object);
	std::map<std::string, Invoker> invokers = INSTANCE->_interpreter->getInvokers();

	size_t maxSize = JSStringGetMaximumUTF8CStringSize(propertyName);
	char buffer[maxSize];
	JSStringGetUTF8CString(propertyName, buffer, maxSize);
	std::string prop(buffer);

	if (invokers.find(prop) != invokers.end()) {
		return INSTANCE->getDataAsValue(invokers.find(prop)->second.getDataModelVariables());
	}
	return JSValueMakeUndefined(ctx);
}

void JSCDataModel::jsInvokerListProps(JSContextRef ctx, JSObjectRef object, JSPropertyNameAccumulatorRef propertyNames) {
	JSCDataModel* INSTANCE = (JSCDataModel*)JSObjectGetPrivate(object);
	std::map<std::string, Invoker> invokers = INSTANCE->_interpreter->getInvokers();

	std::map<std::string, Invoker>::const_iterator invokerIter = invokers.begin();
	while(invokerIter != invokers.end()) {
		JSStringRef invokeName = JSStringCreateWithUTF8CString(invokerIter->first.c_str());
		JSPropertyNameAccumulatorAddName(propertyNames, invokeName);
		JSStringRelease(invokeName);
		invokerIter++;
	}
}

}