#include "uscxml/Common.h"
#include "NULLDataModel.h"

#include "uscxml/Message.h"
#include <glog/logging.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool connect(pluma::Host& host) {
	host.add( new NULLDataModelProvider() );
	return true;
}
#endif

NULLDataModel::NULLDataModel() {
}

boost::shared_ptr<DataModelImpl> NULLDataModel::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<NULLDataModel> dm = boost::shared_ptr<NULLDataModel>(new NULLDataModel());
	dm->_interpreter = interpreter;
	return dm;
}

NULLDataModel::~NULLDataModel() {
}

void NULLDataModel::pushContext() {
}

void NULLDataModel::popContext() {
}

void NULLDataModel::initialize() {
}

void NULLDataModel::setEvent(const Event& event) {
}

Data NULLDataModel::getStringAsData(const std::string& content) {
	Data data;
	return data;
}

bool NULLDataModel::validate(const std::string& location, const std::string& schema) {
	return true;
}

uint32_t NULLDataModel::getLength(const std::string& expr) {
	return 0;
}

void NULLDataModel::setForeach(const std::string& item,
                               const std::string& array,
                               const std::string& index,
                               uint32_t iteration) {
}

void NULLDataModel::eval(const std::string& expr) {
}

bool NULLDataModel::isDeclared(const std::string& expr) {
	return true;
}

/**
 * The boolean expression language consists of the In predicate only. It has the
 * form 'In(id)', where id is the id of a state in the enclosing state machine.
 * The predicate must return 'true' if and only if that state is in the current
 * state configuration.
 */
bool NULLDataModel::evalAsBool(const std::string& expr) {
	std::string trimmedExpr = expr;
	boost::trim(trimmedExpr);
	if (!boost::istarts_with(trimmedExpr, "in"))
		return false;

	// find string in between brackets
	size_t start = trimmedExpr.find_first_of("(");
	size_t end = trimmedExpr.find_last_of(")");
	if (start == std::string::npos || end == std::string::npos || start >= end)
		return false;
	start++;

	// split at comma
	std::stringstream ss(trimmedExpr.substr(start, end - start));
	std::vector<std::string> stateExprs;
	std::string item;
	while(std::getline(ss, item, ',')) {
		stateExprs.push_back(item);
	}

	for (unsigned int i = 0; i < stateExprs.size(); i++) {
		// remove ticks
		size_t start = stateExprs[i].find_first_of("'");
		size_t end = stateExprs[i].find_last_of("'");

		std::string stateName;
		if (start != std::string::npos && end != std::string::npos && start < end) {
			start++;
			stateName = stateExprs[i].substr(start, end - start);
		} else {
			stateName = stateExprs[i];
		}

		if (Interpreter::isMember(_interpreter->getState(stateName), _interpreter->getConfiguration())) {
			continue;
		}
		return false;
	}
	return true;
}

std::string NULLDataModel::evalAsString(const std::string& expr) {
	return expr;
}

double NULLDataModel::evalAsNumber(const std::string& expr) {
	return 0;
}

}