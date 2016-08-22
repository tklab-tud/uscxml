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

#include "WrappedActionLanguage.h"
#include "../../../uscxml/plugins/DataModelImpl.h"

namespace uscxml {

WrappedActionLanguage::WrappedActionLanguage() {}
WrappedActionLanguage::~WrappedActionLanguage() {}

void WrappedActionLanguage::setDataModel(DataModelImpl* dm) {
	std::shared_ptr<DataModelImpl> dmPtr(dm);
	this->dataModel = DataModel(dmPtr);
}

}