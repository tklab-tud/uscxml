#include "uscxml/Common.h"
#include "SWIDataModel.h"
#include "uscxml/Message.h"
#include <glog/logging.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool connect(pluma::Host& host) {
	host.add( new SWIDataModelProvider() );
	return true;
}
#endif

SWIDataModel::SWIDataModel() {
}

DataModelImpl* SWIDataModel::create(Interpreter* interpreter) {
	SWIDataModel* dm = new SWIDataModel();
	dm->_interpreter = interpreter;
	const char* swiPath = SWI_LIBRARY_PATH;
	dm->_plEngine = new PlEngine((char*)swiPath);
	return dm;
}

void SWIDataModel::registerIOProcessor(const std::string& name, const IOProcessor& ioprocessor) {
	std::cout << "SWIDataModel::registerIOProcessor" << std::endl;
}

void SWIDataModel::setSessionId(const std::string& sessionId) {
	std::cout << "SWIDataModel::setSessionId" << std::endl;
	_sessionId = sessionId;
}

void SWIDataModel::setName(const std::string& name) {
	std::cout << "SWIDataModel::setName" << std::endl;
	_name = name;
}

SWIDataModel::~SWIDataModel() {
}

void SWIDataModel::pushContext() {
	std::cout << "SWIDataModel::pushContext" << std::endl;
}

void SWIDataModel::popContext() {
	std::cout << "SWIDataModel::popContext" << std::endl;
}

void SWIDataModel::initialize() {
	std::cout << "SWIDataModel::initialize" << std::endl;
}

void SWIDataModel::setEvent(const Event& event) {
	std::cout << "SWIDataModel::setEvent" << std::endl;
	_event = event;
}

Data SWIDataModel::getStringAsData(const std::string& content) {
	std::cout << "SWIDataModel::getStringAsData" << std::endl;
	Data data;
	return data;
}

bool SWIDataModel::validate(const std::string& location, const std::string& schema) {
	std::cout << "SWIDataModel::validate" << std::endl;
	return true;
}

uint32_t SWIDataModel::getLength(const std::string& expr) {
	std::cout << "SWIDataModel::getLength" << std::endl;
	return 0;
}

void SWIDataModel::eval(const std::string& expr) {
	std::cout << "SWIDataModel::eval" << std::endl;
}

bool SWIDataModel::evalAsBool(const std::string& expr) {
	std::cout << "SWIDataModel::evalAsBool" << std::endl;
	return true;
}

std::string SWIDataModel::evalAsString(const std::string& expr) {
	std::cout << "SWIDataModel::evalAsString" << std::endl;
	return std::string("");
}

void SWIDataModel::assign(const std::string& location, const Data& data) {
	std::cout << "SWIDataModel::assign" << std::endl;
}

void SWIDataModel::assign(const std::string& location, const std::string& expr) {
	std::cout << "SWIDataModel::assign" << std::endl;
}

}