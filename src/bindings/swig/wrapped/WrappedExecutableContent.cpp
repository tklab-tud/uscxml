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

#include "WrappedExecutableContent.h"
#include "uscxml/util/DOM.h"
#include <xercesc/dom/DOM.hpp>
#include <ostream>

namespace uscxml {

WrappedExecutableContent::WrappedExecutableContent() {}
WrappedExecutableContent::~WrappedExecutableContent() {}

void WrappedExecutableContent::enterElement(XERCESC_NS::DOMElement* element) {
	std::stringstream ss;
	ss << *element;
	enterElement(ss.str());
}

void WrappedExecutableContent::exitElement(XERCESC_NS::DOMElement* element) {
	std::stringstream ss;
	ss << *element;
	exitElement(ss.str());
}


}