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

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool connect(pluma::Host& host) {
	host.add( new JSCDataModelProvider() );
	return true;
}
#endif

JSCDataModel::JSCDataModel() {
}

// functions need to be objects to hold private data in JSC
JSClassDefinition JSCDataModel::jsInClassDef = { 0, 0, "In", 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, jsIn, 0, 0, 0 };
JSClassDefinition JSCDataModel::jsPrintClassDef = { 0, 0, "print", 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, jsPrint, 0, 0, 0 };

boost::shared_ptr<DataModelImpl> JSCDataModel::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<JSCDataModel> dm = boost::shared_ptr<JSCDataModel>(new JSCDataModel());

	dm->_ctx = JSGlobalContextCreate(NULL);
	dm->_interpreter = interpreter;

	dm->_dom = new Arabica::DOM::JSCDOM();
	dm->_dom->xpath = new Arabica::XPath::XPath<std::string>();
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

	dm->eval("_ioprocessors = {};");

	Arabica::DOM::JSCDocument::JSCDocumentPrivate* privData = new Arabica::DOM::JSCDocument::JSCDocumentPrivate();
	privData->nativeObj = new Arabica::DOM::Document<std::string>(interpreter->getDocument());
	privData->dom = dm->_dom;

	JSObjectRef documentObject = JSObjectMake(dm->_ctx, Arabica::DOM::JSCDocument::getTmpl(), privData);
	JSObjectRef globalObject = JSContextGetGlobalObject(dm->_ctx);
	JSObjectSetProperty(dm->_ctx, globalObject, JSStringCreateWithUTF8CString("document"), documentObject, kJSPropertyAttributeReadOnly | kJSPropertyAttributeDontDelete, NULL);

	dm->eval("_invokers = {};");
	dm->eval("_x = {};");

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
	Arabica::DOM::JSCSCXMLEvent::JSCSCXMLEventPrivate* privData = new Arabica::DOM::JSCSCXMLEvent::JSCSCXMLEventPrivate();
	privData->nativeObj = new Event(event);
	privData->dom = _dom;

	JSObjectRef eventObj = JSObjectMake(_ctx, Arabica::DOM::JSCSCXMLEvent::getTmpl(), privData);
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
		LOG(ERROR) << "IsUndefined is unimplemented";
		break;
	case kJSTypeNull:
		LOG(ERROR) << "IsNull is unimplemented";
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

void JSCDataModel::eval(const std::string& expr) {
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

void JSCDataModel::assign(const Arabica::DOM::Element<std::string>& assignElem,
                          const Arabica::DOM::Document<std::string>& doc,
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

JSValueRef JSCDataModel::getDocumentAsValue(const Arabica::DOM::Document<std::string>& doc) {

	struct Arabica::DOM::JSCDocument::JSCDocumentPrivate* retPrivData = new Arabica::DOM::JSCDocument::JSCDocumentPrivate();
	retPrivData->dom = _dom;
	retPrivData->nativeObj = new Arabica::DOM::Document<std::string>(doc);

	JSObjectRef retObj = JSObjectMake(_ctx, Arabica::DOM::JSCDocument::getTmpl(), retPrivData);

	return retObj;
}

void JSCDataModel::assign(const std::string& location, const Data& data) {
	std::stringstream ssJSON;
	ssJSON << data;
	evalAsValue(location + " = " + ssJSON.str());
}

void JSCDataModel::init(const Arabica::DOM::Element<std::string>& dataElem,
                        const Arabica::DOM::Document<std::string>& doc,
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

}