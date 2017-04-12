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

#include "Invoker.h"
#include "InvokerImpl.h"

namespace uscxml {

PIMPL_OPERATORS_INHERIT_IMPL(Invoker, EventHandler)

void Invoker::invoke(const std::string& source, const Event& invokeEvent) {
	_impl->invoke(source, invokeEvent);
}

void Invoker::uninvoke()     {
	_impl->uninvoke();
}

void Invoker::eventFromSCXML(const Event& event)     {
	_impl->eventFromSCXML(event);
}

void Invoker::deserialize(const Data& encodedState) {
	return _impl->deserialize(encodedState);
}

Data Invoker::serialize()     {
	return _impl->serialize();
}


}
