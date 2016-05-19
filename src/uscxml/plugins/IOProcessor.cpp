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

#include "IOProcessor.h"
#include "IOProcessorImpl.h"

namespace uscxml {

PIMPL_OPERATORS_INHERIT_IMPL(IOProcessor, EventHandler)

void IOProcessor::eventFromSCXML(const std::string& target, const Event& event) {
	_impl->eventFromSCXML(target, event);
}

bool IOProcessor::isValidTarget(const std::string& target) {
	return _impl->isValidTarget(target);
}


}

