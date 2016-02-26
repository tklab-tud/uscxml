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

#include <boost/algorithm/string.hpp>

#include "uscxml/Common.h"
#include "NULLDataModel.h"
#include "uscxml/dom/DOMUtils.h"

#include "uscxml/Message.h"
#include <glog/logging.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool pluginConnect(pluma::Host& host) {
	host.add( new NULLDataModelProvider() );
	return true;
}
#endif

NULLDataModel::NULLDataModel() {
}

boost::shared_ptr<DataModelImpl> NULLDataModel::create(InterpreterInfo* interpreter) {
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
	Data data = Data::fromJSON(content);
	if (data.empty()) {
		data = Data(content, Data::VERBATIM);
	}
	return data;
}

bool NULLDataModel::validate(const std::string& location, const std::string& schema) {
	return true;
}

bool NULLDataModel::isLocation(const std::string& expr) {
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

void NULLDataModel::eval(const Arabica::DOM::Element<std::string>& scriptElem,
                         const std::string& expr) {
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
bool NULLDataModel::evalAsBool(const Arabica::DOM::Element<std::string>& node, const std::string& expr) {
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
	std::list<std::string> stateExprs;
	std::string item;
	while(std::getline(ss, item, ',')) {
		stateExprs.push_back(item);
	}

	for (std::list<std::string>::const_iterator stateIter = stateExprs.begin(); stateIter != stateExprs.end(); stateIter++) {
		// remove ticks
		size_t start = stateIter->find_first_of("'");
		size_t end = stateIter->find_last_of("'");

		std::string stateName;
		if (start != std::string::npos && end != std::string::npos && start < end) {
			start++;
			stateName = stateIter->substr(start, end - start);
		} else {
			stateName = *stateIter;
		}

		if (_interpreter->isInState(stateName)) {
			continue;
		}
		return false;
	}
	return true;
}

std::string NULLDataModel::evalAsString(const std::string& expr) {
	return expr;
}


}