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

#ifndef WRAPPEDACTIONLANGUAGE_H_020AFC96
#define WRAPPEDACTIONLANGUAGE_H_020AFC96

#include <vector>
#include <list>
#include <ostream>
#include <string>

#include <xercesc/dom/DOM.hpp>

#include "../../../uscxml/Interpreter.h"

namespace uscxml {

class DataModelImpl;

class WrappedActionLanguage : public ActionLanguage {
public:

	WrappedActionLanguage();
	virtual ~WrappedActionLanguage();

	void setDataModel(DataModelImpl* dm);
};

}

#endif /* end of include guard: WRAPPEDACTIONLANGUAGE_H_020AFC96 */
