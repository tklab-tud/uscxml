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

#include "InterpreterFast.h"

#include "uscxml/Factory.h"
#include "uscxml/concurrency/DelayedEventQueue.h"

#include <glog/logging.h>
#include "uscxml/UUID.h"
#include "uscxml/dom/DOMUtils.h"

namespace uscxml {

using namespace Arabica::XPath;
using namespace Arabica::DOM;


void InterpreterFast::handleDOMEvent(Arabica::DOM::Events::Event<std::string>& event) {
	InterpreterImpl::handleDOMEvent(event);

	if (event.getType().compare("DOMAttrModified") == 0) // we do not care about attributes
		return;

}
}