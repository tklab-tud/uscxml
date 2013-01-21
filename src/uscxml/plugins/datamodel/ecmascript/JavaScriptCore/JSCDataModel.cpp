#include "uscxml/Common.h"
#include "JSCDataModel.h"
#include "dom/JSCDOM.h"
#include "dom/JSCDocument.h"

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

boost::shared_ptr<DataModelImpl> JSCDataModel::create(Interpreter* interpreter) {
	boost::shared_ptr<JSCDataModel> dm = boost::shared_ptr<JSCDataModel>(new JSCDataModel());

	dm->_ctx = JSGlobalContextCreate(NULL);
	dm->_interpreter = interpreter;

	Arabica::DOM::JSCDOM* dom = new Arabica::DOM::JSCDOM();
	//  dom->interpreter = interpreter;
	dom->xpath = new Arabica::XPath::XPath<std::string>();
	dom->xpath->setNamespaceContext(interpreter->getNSContext());


	dm->setName(interpreter->getName());
	dm->setSessionId(interpreter->getSessionId());
	dm->eval("_ioprocessors = {};");

	Arabica::DOM::JSCDocument::JSCDocumentPrivate* privData = new Arabica::DOM::JSCDocument::JSCDocumentPrivate();
	privData->arabicaThis = new Arabica::DOM::Document<std::string>(interpreter->getDocument());
	privData->dom = dom;

	JSObjectRef documentObject = JSObjectMake(dm->_ctx, Arabica::DOM::JSCDocument::getTmpl(), privData);
	JSObjectRef globalObject = JSContextGetGlobalObject(dm->_ctx);
	JSObjectSetProperty(dm->_ctx, globalObject, JSStringCreateWithUTF8CString("document"), documentObject, kJSPropertyAttributeReadOnly | kJSPropertyAttributeDontDelete, NULL);

	return dm;
}

void JSCDataModel::registerIOProcessor(const std::string& name, const IOProcessor& ioprocessor) {
	assign("_ioprocessors['" + name + "']", ioprocessor.getDataModelVariables());
}

void JSCDataModel::setSessionId(const std::string& sessionId) {
	_sessionId = sessionId;
}

void JSCDataModel::setName(const std::string& name) {
	_name = name;
}

JSCDataModel::~JSCDataModel() {
	JSGlobalContextRelease(_ctx);
}

void JSCDataModel::pushContext() {
}

void JSCDataModel::popContext() {
}

void JSCDataModel::initialize() {
}

void JSCDataModel::setEvent(const Event& event) {
	LOG(ERROR) << "setEvent not implemented in JSC";
}

Data JSCDataModel::getStringAsData(const std::string& content) {
	JSValueRef result = evalAsValue(content);
	Data data = getValueAsData(result);
	return data;
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

		char* buf = (char*)malloc(JSStringGetMaximumUTF8CStringSize(stringValue));
		JSStringGetUTF8CString(stringValue, buf, sizeof(buf));
		data.atom = std::string(buf, sizeof(buf));
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
			char* buf = (char*)malloc(JSStringGetMaximumUTF8CStringSize(stringValue));
			JSStringGetUTF8CString(stringValue, buf, sizeof(buf));
			std::string property(buf, sizeof(buf));
			if (!isNumeric(property.c_str(), 10))
				isArray = false;
			propertySet.insert(property);
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
	LOG(ERROR) << "I am not sure whether getLength() works :(";
	JSValueRef result = evalAsValue(expr);
	JSValueRef exception = NULL;
	double length = JSValueToNumber(_ctx, result, &exception);
	if (exception)
		handleException(exception);

	return (uint32_t)length;
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

	char* data = (char*)malloc(JSStringGetMaximumUTF8CStringSize(stringValue));
	JSStringGetUTF8CString(stringValue, data, sizeof(data));
	std::string retString(data, sizeof(data));

	JSStringRelease(stringValue);
	free(data);
	return retString;
}

JSValueRef JSCDataModel::evalAsValue(const std::string& expr) {
	JSStringRef scriptJS = JSStringCreateWithUTF8CString(expr.c_str());
	JSValueRef exception = NULL;
	JSValueRef result = JSEvaluateScript(_ctx, scriptJS, NULL, NULL, 0, &exception);
	if (exception)
		handleException(exception);

	JSStringRelease(scriptJS);
	return result;
}

void JSCDataModel::assign(const std::string& location, const Data& data) {
	std::stringstream ssJSON;
	ssJSON << data;
	assign(location, ssJSON.str());
}

void JSCDataModel::assign(const std::string& location, const std::string& expr) {
	evalAsValue(location + " = " + expr);
}

void JSCDataModel::handleException(JSValueRef exception) {
	assert(false);
}

}