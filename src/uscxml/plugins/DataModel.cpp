/**
 *  @file
 *  @author     2012-2014 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#include "DataModel.h"
#include "DataModelImpl.h"

namespace uscxml {

std::list<std::string> DataModel::getNames() {
	return _impl->getNames();
}

bool DataModel::isValidSyntax(const std::string& expr) {
	return _impl->isValidSyntax(expr);
}

bool DataModel::isLegalDataValue(const std::string& expr) {
	return _impl->isLegalDataValue(expr);
}

void DataModel::setEvent(const Event& event) {
	return _impl->setEvent(event);
}

Data DataModel::getAsData(const std::string& content) {
	return _impl->getAsData(content);
}

Data DataModel::evalAsData(const std::string& content) {
	return _impl->evalAsData(content);
}

void DataModel::eval(const std::string& content) {
	_impl->eval(content);
}

bool DataModel::evalAsBool(const std::string& expr) {
	return _impl->evalAsBool(expr);
}

uint32_t DataModel::getLength(const std::string& expr) {
	return _impl->getLength(expr);
}

void DataModel::setForeach(const std::string& item,
                           const std::string& array,
                           const std::string& index,
                           uint32_t iteration) {
	return _impl->setForeach(item, array, index, iteration);
}

void DataModel::assign(const std::string& location, const Data& data, const std::map<std::string, std::string>& attr) {
	return _impl->assign(location, data, attr);
}

void DataModel::init(const std::string& location, const Data& data, const std::map<std::string, std::string>& attr) {
	return _impl->init(location, data, attr);
}

bool DataModel::isDeclared(const std::string& expr) {
	return _impl->isDeclared(expr);
}

size_t DataModel::replaceExpressions(std::string& content) {
	return _impl->replaceExpressions(content);
}

void DataModel::addExtension(DataModelExtension* ext) {
	return _impl->addExtension(ext);
}


}

