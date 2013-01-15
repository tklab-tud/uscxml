#include "uscxml/Common.h"
#include "JSCDataModel.h"
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
	dm->_interpreter = interpreter;

	dm->setName(interpreter->getName());
	dm->setSessionId(interpreter->getSessionId());
	dm->eval("_ioprocessors = {};");

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
}

void JSCDataModel::pushContext() {
}

void JSCDataModel::popContext() {
}

void JSCDataModel::initialize() {
}

void JSCDataModel::setEvent(const Event& event) {
}

Data JSCDataModel::getStringAsData(const std::string& content) {
}

Data JSCDataModel::getValueAsData(const JSC::Handle<JSC::Value>& value) {
}

bool JSCDataModel::validate(const std::string& location, const std::string& schema) {
	return true;
}

uint32_t JSCDataModel::getLength(const std::string& expr) {
}

void JSCDataModel::eval(const std::string& expr) {
}

bool JSCDataModel::evalAsBool(const std::string& expr) {
}

std::string JSCDataModel::evalAsString(const std::string& expr) {
}

void JSCDataModel::assign(const std::string& location, const Data& data) {
}

void JSCDataModel::assign(const std::string& location, const std::string& expr) {
}

}