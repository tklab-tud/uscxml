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
#include "uscxml/util/URL.h"
#include "uscxml/util/String.h"

#include "JSCDataModel.h"
//#include "JSCSCXMLEvent.h"

#include "uscxml/messages/Event.h"
#include "uscxml/util/DOM.h"
#include "uscxml/interpreter/Logging.h"

#include <boost/algorithm/string.hpp>

#define EVENT_STRING_OR_UNDEF(field, cond) \
JSStringRef field##Name = JSStringCreateWithUTF8CString( #field ); \
JSStringRef field##Val = JSStringCreateWithUTF8CString(event.field.c_str()); \
JSObjectSetProperty(_ctx, \
                    eventObj, \
                    field##Name, \
                    (cond ? JSValueMakeString(_ctx, field##Val) : JSValueMakeUndefined(_ctx)), \
                    0, \
                    &exception); \
JSStringRelease(field##Name); \
JSStringRelease(field##Val); \
if (exception) \
    handleException(exception);


using namespace XERCESC_NS;

static JSValueRef XMLString2JS(const XMLCh* input, JSContextRef context) {
	JSValueRef output;

	char* res = XERCESC_NS::XMLString::transcode(input);

	JSStringRef stringRef = JSStringCreateWithUTF8CString(res);
	output = JSValueMakeString(context, stringRef);
	JSStringRelease(stringRef);

	return output;
}

static XMLCh* JS2XMLString(JSValueRef input, JSContextRef context) {

	if (!JSValueIsString(context, input))
		return NULL;

	JSValueRef exception = NULL;
	JSStringRef stringInput = JSValueToStringCopy(context, input, &exception);

	// TODO: I am leaking!
	size_t maxSize = JSStringGetMaximumUTF8CStringSize(stringInput);
	char* output = new char[maxSize + 1];

	JSStringGetUTF8CString(stringInput, output, maxSize);
	XMLCh* ret = XERCESC_NS::XMLString::transcode(output);

	return(ret);
}

#include "JSCDOM.cpp.inc"

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool pluginConnect(pluma::Host& host) {
	host.add( new JSCDataModelProvider() );
	return true;
}
#endif

JSCDataModel::JSCDataModel() {
	_ctx = NULL;
}

JSCDataModel::~JSCDataModel() {
	if (_ctx)
		JSGlobalContextRelease(_ctx);
}

void JSCDataModel::addExtension(DataModelExtension* ext) {
	if (_extensions.find(ext) != _extensions.end())
		return;

	ext->dm = this;
	_extensions.insert(ext);

	JSObjectRef currScope = JSContextGetGlobalObject(_ctx);
	std::list<std::string> locPath = tokenize(ext->provides(), '.');
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

// functions need to be objects to hold private data in JSC
JSClassDefinition JSCDataModel::jsInClassDef = { 0, 0, "In", 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, jsIn, 0, 0, 0 };
JSClassDefinition JSCDataModel::jsPrintClassDef = { 0, 0, "print", 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, jsPrint, 0, 0, 0 };
JSClassDefinition JSCDataModel::jsExtensionClassDef = { 0, 0, "Extension", 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, jsExtension, 0, 0, 0 };

JSClassDefinition JSCDataModel::jsIOProcessorsClassDef = { 0, 0, "ioProcessors", 0, 0, 0, 0, 0, jsIOProcessorHasProp, jsIOProcessorGetProp, 0, 0, jsIOProcessorListProps, 0, 0, 0, 0 };
JSClassDefinition JSCDataModel::jsInvokersClassDef = { 0, 0, "invokers", 0, 0, 0, 0, 0, jsInvokerHasProp, jsInvokerGetProp, 0, 0, jsInvokerListProps, 0, 0, 0, 0 };

std::mutex JSCDataModel::_initMutex;

bool JSCNodeListHasPropertyCallback(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName) {
	size_t propMaxSize = JSStringGetMaximumUTF8CStringSize(propertyName);
	char* propBuffer = new char[propMaxSize];
	JSStringGetUTF8CString(propertyName, propBuffer, propMaxSize);
	std::string propName(propBuffer);
	free(propBuffer);

	std::string base = "0123456789";
	if (propName.find_first_not_of(base) != std::string::npos) {
		return false;
	}

	int index = strTo<int>(propName);
	SwigPrivData* t = (SwigPrivData*) JSObjectGetPrivate(object);
	DOMNodeList* nodeList = (DOMNodeList*)t->swigCObject;

	if (nodeList->getLength() < index) {
		return false;
	}

	return true;
}

JSValueRef JSCNodeListGetPropertyCallback(JSContextRef context, JSObjectRef object, JSStringRef propertyName, JSValueRef* exception) {
	size_t propMaxSize = JSStringGetMaximumUTF8CStringSize(propertyName);
	char* propBuffer = new char[propMaxSize];
	JSStringGetUTF8CString(propertyName, propBuffer, propMaxSize);
	std::string propName(propBuffer);
	free(propBuffer);

	std::string base = "0123456789";
	if (propName.find_first_not_of(base) != std::string::npos) {
		return JSValueMakeUndefined(context);
	}

	int index = strTo<int>(propName);
	SwigPrivData* t = (SwigPrivData*) JSObjectGetPrivate(object);
	DOMNodeList* nodeList = (DOMNodeList*)t->swigCObject;

	if (nodeList->getLength() < index) {
		return JSValueMakeUndefined(context);
	}

	DOMNode* node = nodeList->item(index);
	JSValueRef jsresult = SWIG_NewPointerObj(SWIG_as_voidptr(node),
	                      SWIG_TypeDynamicCast(SWIGTYPE_p_XERCES_CPP_NAMESPACE__DOMNode, SWIG_as_voidptrptr(&node)), 0);
	return jsresult;
}

std::shared_ptr<DataModelImpl> JSCDataModel::create(DataModelCallbacks* callbacks) {
	std::shared_ptr<JSCDataModel> dm(new JSCDataModel());

	dm->_ctx = JSGlobalContextCreate(NULL);
	dm->_callbacks = callbacks;

	JSObjectRef exports;

	// register subscript operator with nodelist
	_exports_DOMNodeList_objectDefinition.hasProperty = JSCNodeListHasPropertyCallback;
	_exports_DOMNodeList_objectDefinition.getProperty = JSCNodeListGetPropertyCallback;

	// not thread safe!
	{
		std::lock_guard<std::mutex> lock(_initMutex);
		JSCDOM_initialize(dm->_ctx, &exports);
	}

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
	JSStringRef name = JSStringCreateWithUTF8CString(dm->_callbacks->getName().c_str());
	JSObjectSetProperty(dm->_ctx, JSContextGetGlobalObject(dm->_ctx), nameName, JSValueMakeString(dm->_ctx, name), kJSPropertyAttributeReadOnly | kJSPropertyAttributeDontDelete, NULL);
	JSStringRelease(nameName);
	JSStringRelease(name);

	JSStringRef sessionIdName = JSStringCreateWithUTF8CString("_sessionid");
	JSStringRef sessionId = JSStringCreateWithUTF8CString(dm->_callbacks->getSessionId().c_str());
	JSObjectSetProperty(dm->_ctx, JSContextGetGlobalObject(dm->_ctx), sessionIdName, JSValueMakeString(dm->_ctx, sessionId), kJSPropertyAttributeReadOnly | kJSPropertyAttributeDontDelete, NULL);
	JSStringRelease(sessionIdName);
	JSStringRelease(sessionId);

	dm->evalAsValue("_x = {};");

	return dm;
}

void JSCDataModel::setEvent(const Event& event) {
	Event* evPtr = new Event(event);

	JSObjectRef eventObj = SWIG_JSC_NewPointerObj(_ctx, evPtr, SWIGTYPE_p_uscxml__Event, SWIG_POINTER_OWN);
	JSObjectRef globalObject = JSContextGetGlobalObject(_ctx);

	JSValueRef exception = NULL;

	/* Manually handle swig ignored fields */
	EVENT_STRING_OR_UNDEF(sendid, !event.hideSendId); // test333
	EVENT_STRING_OR_UNDEF(origin, event.origin.size() > 0); // test335
	EVENT_STRING_OR_UNDEF(origintype, event.origintype.size() > 0); // test337
	EVENT_STRING_OR_UNDEF(invokeid, event.invokeid.size() > 0); // test339

	/* Manually handle swig ignored event type */
	JSStringRef eventTypeName = JSStringCreateWithUTF8CString("type");
	JSStringRef eventTypeVal;

	// test 331
	switch (event.eventType) {
	case Event::EXTERNAL:
		eventTypeVal = JSStringCreateWithUTF8CString("external");
		break;
	case Event::INTERNAL:
		eventTypeVal = JSStringCreateWithUTF8CString("internal");
		break;
	case Event::PLATFORM:
		eventTypeVal = JSStringCreateWithUTF8CString("platform");
		break;
	}

	JSObjectSetProperty(_ctx, eventObj, eventTypeName, JSValueMakeString(_ctx, eventTypeVal), 0, &exception);
	if (exception)
		handleException(exception);

	JSStringRelease(eventTypeName);
	JSStringRelease(eventTypeVal);

	/* Manually handle swig ignored event data */
	if (event.data.node) {
		JSStringRef propName = JSStringCreateWithUTF8CString("data");
		JSObjectSetProperty(_ctx, eventObj, propName, getNodeAsValue(event.data.node), 0, &exception);
		JSStringRelease(propName);
		if (exception)
			handleException(exception);
#if 0
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
			JSStringRef contentStr = JSStringCreateWithUTF8CString(spaceNormalize(event.content).c_str());
			JSObjectSetProperty(_ctx, eventObj, propName, JSValueMakeString(_ctx, contentStr), 0, &exception);
			JSStringRelease(propName);
			JSStringRelease(contentStr);

			if (exception)
				handleException(exception);
		}
#endif
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

Data JSCDataModel::evalAsData(const std::string& content) {
	JSValueRef result = evalAsValue(content);
	return getValueAsData(result);
}

Data JSCDataModel::getAsData(const std::string& content) {
	// parse as JSON test 578
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

JSValueRef JSCDataModel::getDataAsValue(const Data& data) {
	JSValueRef exception = NULL;

	if (data.node) {
		return getNodeAsValue(data.node);
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
//	if (data.binary) {
//		uscxml::ArrayBuffer* localInstance = new uscxml::ArrayBuffer(data.binary);
//
//		JSClassRef retClass = JSCArrayBuffer::getTmpl();
//		struct JSCArrayBuffer::JSCArrayBufferPrivate* retPrivData = new JSCArrayBuffer::JSCArrayBufferPrivate();
//		retPrivData->nativeObj = localInstance;
//
//		JSObjectRef retObj = JSObjectMake(_ctx, retClass, retPrivData);
//		return retObj;
//	}
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
//		if (JSValueIsObjectOfClass(_ctx, value, JSCArrayBuffer::getTmpl())) {
//			// binary data
//			JSCArrayBuffer::JSCArrayBufferPrivate* privObj = (JSCArrayBuffer::JSCArrayBufferPrivate*)JSObjectGetPrivate(objValue);
//			data.binary = privObj->nativeObj->_blob;
//			return data;
//		} else

		if (JSValueIsObjectOfClass(_ctx, value, _exports_DOMNode_classRef)) {
			// dom node
			void* privData = NULL;
			SWIG_JSC_ConvertPtr(_ctx, value, &privData, SWIGTYPE_p_XERCES_CPP_NAMESPACE__DOMNode, 0);
			data.node = (XERCESC_NS::DOMNode*)privData;
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

#if 0
bool JSCDataModel::isLocation(const std::string& expr) {
	// location needs to be LHS and ++ is only valid for LHS
	return isValidSyntax(expr + "++");
}
#endif

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

bool JSCDataModel::evalAsBool(const std::string& expr) {
	JSValueRef result = evalAsValue(expr);
	return JSValueToBoolean(_ctx, result);
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

JSValueRef JSCDataModel::getNodeAsValue(const DOMNode* node) {
	return SWIG_JSC_NewPointerObj(_ctx,
	                              (void*)node,
	                              SWIG_TypeDynamicCast(SWIGTYPE_p_XERCES_CPP_NAMESPACE__DOMNode,
	                                      SWIG_as_voidptrptr(&node)),
	                              0);

//    switch (node->getNodeType()) {
//    case DOMNode::ELEMENT_NODE:
//        return SWIG_JSC_NewPointerObj(_ctx, (void*)node, SWIGTYPE_p_XERCES_CPP_NAMESPACE__DOMElement, 0);
//        break;
//
//    case DOMNode::COMMENT_NODE:
//        return SWIG_JSC_NewPointerObj(_ctx, (void*)node, SWIGTYPE_p_XERCES_CPP_NAMESPACE__DOMComment, 0);
//        break;
//
//    // TODO: We need to dispatch more types here!
//    default:
//        return SWIG_JSC_NewPointerObj(_ctx, (void*)node, SWIGTYPE_p_XERCES_CPP_NAMESPACE__DOMNode, 0);
//        break;
//    }
}

void JSCDataModel::assign(const std::string& location, const Data& data) {

	// flags on attribute are ignored?
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

	JSValueRef exception = NULL;
	if (data.node) {
		JSObjectSetProperty(_ctx, JSContextGetGlobalObject(_ctx), JSStringCreateWithUTF8CString(location.c_str()), getNodeAsValue(data.node), 0, &exception);
	} else {
		evalAsValue(location + " = " + Data::toJSON(data));
	}

	/**
	 * test157: We need to evaluate, as this will not throw for 'continue' = Var[5] in
	 */
//    JSObjectSetProperty(_ctx, JSContextGetGlobalObject(_ctx), JSStringCreateWithUTF8CString(location.c_str()), getDataAsValue(data), 0, &exception);

	if (exception)
		handleException(exception);
}

void JSCDataModel::init(const std::string& location, const Data& data) {
	try {
		assign(location, data);
	} catch (ErrorEvent e) {
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

			if (INSTANCE->_callbacks->isInState(stateName)) {
				continue;
			}
		}
		return JSValueMakeBoolean(ctx, false);
	}
	return JSValueMakeBoolean(ctx, true);

}

bool JSCDataModel::jsIOProcessorHasProp(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName) {
	JSCDataModel* INSTANCE = (JSCDataModel*)JSObjectGetPrivate(object);
	std::map<std::string, IOProcessor> ioProcessors = INSTANCE->_callbacks->getIOProcessors();

	size_t maxSize = JSStringGetMaximumUTF8CStringSize(propertyName);
	char buffer[maxSize];
	JSStringGetUTF8CString(propertyName, buffer, maxSize);
	std::string prop(buffer);

	return ioProcessors.find(prop) != ioProcessors.end();
}

JSValueRef JSCDataModel::jsIOProcessorGetProp(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef* exception) {
	JSCDataModel* INSTANCE = (JSCDataModel*)JSObjectGetPrivate(object);
	std::map<std::string, IOProcessor> ioProcessors = INSTANCE->_callbacks->getIOProcessors();

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
	std::map<std::string, IOProcessor> ioProcessors = INSTANCE->_callbacks->getIOProcessors();

	std::map<std::string, IOProcessor>::const_iterator ioProcIter = ioProcessors.begin();
	while(ioProcIter != ioProcessors.end()) {
		JSStringRef ioProcName = JSStringCreateWithUTF8CString(ioProcIter->first.c_str());
		JSPropertyNameAccumulatorAddName(propertyNames, ioProcName);
		ioProcIter++;
	}
}


bool JSCDataModel::jsInvokerHasProp(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName) {
	JSCDataModel* INSTANCE = (JSCDataModel*)JSObjectGetPrivate(object);
	std::map<std::string, Invoker> invokers = INSTANCE->_callbacks->getInvokers();

	size_t maxSize = JSStringGetMaximumUTF8CStringSize(propertyName);
	char buffer[maxSize];
	JSStringGetUTF8CString(propertyName, buffer, maxSize);
	std::string prop(buffer);

	return invokers.find(prop) != invokers.end();
}

JSValueRef JSCDataModel::jsInvokerGetProp(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef* exception) {
	JSCDataModel* INSTANCE = (JSCDataModel*)JSObjectGetPrivate(object);
	std::map<std::string, Invoker> invokers = INSTANCE->_callbacks->getInvokers();

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
	std::map<std::string, Invoker> invokers = INSTANCE->_callbacks->getInvokers();

	std::map<std::string, Invoker>::const_iterator invokerIter = invokers.begin();
	while(invokerIter != invokers.end()) {
		JSStringRef invokeName = JSStringCreateWithUTF8CString(invokerIter->first.c_str());
		JSPropertyNameAccumulatorAddName(propertyNames, invokeName);
		JSStringRelease(invokeName);
		invokerIter++;
	}
}

}
