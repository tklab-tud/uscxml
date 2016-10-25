/**
 *  @file
 *  @author     2016 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#include "C89DataModel.h"

#include "uscxml/messages/Event.h"
#include "uscxml/util/DOM.h"
#include <easylogging++.h>

namespace uscxml {

C89DataModel::C89DataModel() {
}

std::shared_ptr<DataModelImpl> C89DataModel::create(DataModelCallbacks* callbacks) {
	std::shared_ptr<C89DataModel> dm(new C89DataModel());
	PicocInitialise(&dm->_pc, PICOC_STACK_SIZE);
	PicocIncludeAllSystemHeaders(&dm->_pc);
	return dm;
}

C89DataModel::~C89DataModel() {
	PicocCleanup(&_pc);
}

void C89DataModel::addExtension(DataModelExtension* ext) {
	ERROR_EXECUTION_THROW("Extensions unimplemented in C89 datamodel");
}

void C89DataModel::setEvent(const Event& event) {
}

Data C89DataModel::evalAsData(const std::string& content) {
	Data data;
	return data;
}

bool C89DataModel::isValidSyntax(const std::string& expr) {
	return true;
}

uint32_t C89DataModel::getLength(const std::string& expr) {
	return 0;
}

void C89DataModel::setForeach(const std::string& item,
                              const std::string& array,
                              const std::string& index,
                              uint32_t iteration) {
}

bool C89DataModel::isDeclared(const std::string& expr) {
	return true;
}


void C89DataModel::assign(const std::string& location, const Data& data) {
}

void C89DataModel::init(const std::string& location, const Data& data) {
}

bool C89DataModel::evalAsBool(const std::string& expr) {
	return false;
}

Data C89DataModel::getAsData(const std::string& content) {
	Data data;
	return data;
}


std::string C89DataModel::andExpressions(std::list<std::string> exprs) {
	return "";
}


}
