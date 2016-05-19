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

#include "ExecutableContent.h"
#include "ExecutableContentImpl.h"

#include <xercesc/dom/DOM.hpp>
#include <string>
#include <memory>
#include <sstream>

namespace uscxml {

std::string ExecutableContent::getLocalName() {
	return _impl->getLocalName();
}

std::string ExecutableContent::getNamespace() {
	return _impl->getNamespace();
}

void ExecutableContent::enterElement(XERCESC_NS::DOMElement* node) {
	return _impl->enterElement(node);
}

void ExecutableContent::exitElement(XERCESC_NS::DOMElement* node) {
	return _impl->exitElement(node);
}

bool ExecutableContent::processChildren() {
	return _impl->processChildren();
}

}
