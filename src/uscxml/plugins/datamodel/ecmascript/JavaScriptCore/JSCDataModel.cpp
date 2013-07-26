#include "uscxml/Common.h"
#include "JSCDataModel.h"
#include "dom/JSCDOM.h"
#include "dom/JSCDocument.h"
#include "dom/JSCSCXMLEvent.h"

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
	host.add( new JSCDataModelProvider() );
	return true;
}
#endif

JSCDataModel::JSCDataModel() {
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

JSClassDefinition JSCDataModel::jsIOProcessorsClassDef = { 0, 0, "ioProcessors", 0, 0, 0, 0, 0, jsIOProcessorHasProp, jsIOProcessorGetProp, 0, 0, jsIOProcessorListProps, 0, 0, 0, 0 };
JSClassDefinition JSCDataModel::jsInvokersClassDef = { 0, 0, "invokers", 0, 0, 0, 0, 0, jsInvokerHasProp, jsInvokerGetProp, 0, 0, jsInvokerListProps, 0, 0, 0, 0 };

boost::shared_ptr<DataModelImpl> JSCDataModel::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<JSCDataModel> dm = boost::shared_ptr<JSCDataModel>(new JSCDataModel());

	dm->_ctx = JSGlobalContextCreate(NULL);
	dm->_interpreter = interpreter;

	dm->_dom = new JSCDOM();
	dm->_dom->xpath = new XPath<std::string>();
	dm->_dom->xpath->setNamespaceContext(interpreter->getNSContext());

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
	JSStringRelease(inName);

	JSClassRef jsInvokerClassRef = JSClassCreate(&jsInvokersClassDef);
	JSObjectRef jsInvoker = JSObjectMake(dm->_ctx, jsInvokerClassRef, dm.get());
	JSStringRef invokerName = JSStringCreateWithUTF8CString("_invokers");
	JSObjectSetProperty(dm->_ctx, JSContextGetGlobalObject(dm->_ctx), invokerName, jsInvoker, kJSPropertyAttributeNone, NULL);
	JSStringRelease(invokerName);

	JSClassRef jsIOProcClassRef = JSClassCreate(&jsIOProcessorsClassDef);
	JSObjectRef jsIOProc = JSObjectMake(dm->_ctx, jsIOProcClassRef, dm.get());
	JSStringRef ioProcName = JSStringCreateWithUTF8CString("_ioprocessors");
	JSObjectSetProperty(dm->_ctx, JSContextGetGlobalObject(dm->_ctx), ioProcName, jsIOProc, kJSPropertyAttributeNone, NULL);
	JSStringRelease(ioProcName);

	JSStringRef nameName = JSStringCreateWithUTF8CString("_name");
	JSStringRef name = JSStringCreateWithUTF8CString(dm->_interpreter->getName().c_str());
	JSObjectSetProperty(dm->_ctx, JSContextGetGlobalObject(dm->_ctx), nameName, JSValueMakeString(dm->_ctx, name), kJSPropertyAttributeNone, NULL);
	JSStringRelease(nameName);
	JSStringRelease(name);

	JSStringRef sessionIdName = JSStringCreateWithUTF8CString("_sessionid");
	JSStringRef sessionId = JSStringCreateWithUTF8CString(dm->_interpreter->getSessionId().c_str());
	JSObjectSetProperty(dm->_ctx, JSContextGetGlobalObject(dm->_ctx), sessionIdName, JSValueMakeString(dm->_ctx, sessionId), kJSPropertyAttributeNone, NULL);
	JSStringRelease(sessionIdName);
	JSStringRelease(sessionId);

	JSCDocument::JSCDocumentPrivate* privData = new JSCDocument::JSCDocumentPrivate();
	if (interpreter) {
		privData->nativeObj = new Document<std::string>(interpreter->getDocument());
		privData->dom = dm->_dom;

		JSObjectRef documentObject = JSObjectMake(dm->_ctx, JSCDocument::getTmpl(), privData);
		JSObjectRef globalObject = JSContextGetGlobalObject(dm->_ctx);
		JSObjectSetProperty(dm->_ctx, globalObject, JSStringCreateWithUTF8CString("document"), documentObject, kJSPropertyAttributeReadOnly | kJSPropertyAttributeDontDelete, NULL);
	}

	dm->eval(Element<std::string>(), "_x = {};");

	return dm;
}

JSCDataModel::~JSCDataModel() {
	JSGlobalContextRelease(_ctx);
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

	if (event.dom) {
		JSStringRef propName = JSStringCreateWithUTF8CString("data");
		JSObjectSetProperty(_ctx, eventObj, propName, getDocumentAsValue(event.dom), 0, &exception);
		JSStringRelease(propName);
		if (exception)
			handleException(exception);

	} else if (event.content.length() > 0) {
		// _event.data is a string or JSON
		Data json = Data::fromJSON(event.content);
		if (json) {
			JSStringRef propName = JSStringCreateWithUTF8CString("data");
			JSObjectSetProperty(_ctx, eventObj, propName, getDataAsValue(json), 0, &exception);
			JSStringRelease(propName);
			if (exception)
				handleException(exception);
		} else {
			JSStringRef propName = JSStringCreateWithUTF8CString("data");
			JSStringRef contentStr = JSStringCreateWithUTF8CString(Interpreter::spaceNormalize(event.content).c_str());
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
		if (eventCopy.data > 0) {
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

	JSObjectSetProperty(_ctx, globalObject, JSStringCreateWithUTF8CString("_event"), eventObj, kJSPropertyAttributeDontDelete, &exception);
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
	if (data.type == Data::VERBATIM) {
		JSStringRef stringRef = JSStringCreateWithUTF8CString(data.atom.c_str());
		JSValueRef value = JSValueMakeString(_ctx, stringRef);
		JSStringRelease(stringRef);
		return value;
	} else {
		return evalAsValue(data.atom);
	}
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
			JSStringRelease(stringValue);
			free(buf);
		}
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
//	LOG(ERROR) << "I am not sure whether getLength() works :(";
	JSValueRef result = evalAsValue("(" + expr + ").length");
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
	assign(item, ss.str());
	if (index.length() > 0) {
		// assign iteration element to index
		std::stringstream ss;
		ss << iteration;
		assign(index, ss.str());
	}
}

bool JSCDataModel::isDeclared(const std::string& expr) {
	return true;
}

void JSCDataModel::eval(const Element<std::string>& scriptElem,
												const std::string& expr) {
	evalAsValue(expr);
}

bool JSCDataModel::evalAsBool(const std::string& expr) {
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
                          const Document<std::string>& doc,
                          const std::string& content) {
	std::string key;
	JSValueRef exception = NULL;
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
		JSObjectSetProperty(_ctx, JSContextGetGlobalObject(_ctx), JSStringCreateWithUTF8CString(key.c_str()), getDocumentAsValue(doc), 0, &exception);
		if (exception)
			handleException(exception);
	} else if (content.size() > 0) {
		try {
			evalAsValue(key + " = " + content);
		} catch (...) {
			evalAsValue(key + " = " + "\"" + Interpreter::spaceNormalize(content) + "\"");
		}
	} else {
		JSObjectSetProperty(_ctx, JSContextGetGlobalObject(_ctx), JSStringCreateWithUTF8CString(key.c_str()), JSValueMakeUndefined(_ctx), 0, &exception);
		if (exception)
			handleException(exception);
	}
}

JSValueRef JSCDataModel::getDocumentAsValue(const Document<std::string>& doc) {

	struct JSCDocument::JSCDocumentPrivate* retPrivData = new JSCDocument::JSCDocumentPrivate();
	retPrivData->dom = _dom;
	retPrivData->nativeObj = new Document<std::string>(doc);

	JSObjectRef retObj = JSObjectMake(_ctx, JSCDocument::getTmpl(), retPrivData);

	return retObj;
}

void JSCDataModel::assign(const std::string& location, const Data& data) {
	std::stringstream ssJSON;
	ssJSON << data;
	evalAsValue(location + " = " + ssJSON.str());
}

void JSCDataModel::init(const Element<std::string>& dataElem,
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

void JSCDataModel::handleException(JSValueRef exception) {
	JSStringRef exceptionStringRef = JSValueToStringCopy(_ctx, exception, NULL);
	size_t maxSize = JSStringGetMaximumUTF8CStringSize(exceptionStringRef);
	char buffer[maxSize];
	JSStringGetUTF8CString(exceptionStringRef, buffer, maxSize);
	JSStringRelease(exceptionStringRef);
	std::string exceptionMsg(buffer);

	Event exceptionEvent;
	exceptionEvent.data.compound["exception"] = Data(exceptionMsg, Data::VERBATIM);
	exceptionEvent.name = "error.execution";
	exceptionEvent.type = Event::PLATFORM;

	throw(exceptionEvent);

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
			std::string msg(buffer);

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
			std::string stateName(buffer);
			if (Interpreter::isMember(INSTANCE->_interpreter->getState(stateName), INSTANCE->_interpreter->getConfiguration())) {
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
		invokerIter++;
	}	
}

}