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


#include "ContentExecutor.h"
#include "ContentExecutorImpl.h"

namespace uscxml {

void ContentExecutor::process(XERCESC_NS::DOMElement* block) {
	_impl->process(block);
}

void ContentExecutor::invoke(XERCESC_NS::DOMElement* invoke) {
	_impl->invoke(invoke);
}

void ContentExecutor::uninvoke(XERCESC_NS::DOMElement* invoke) {
	_impl->uninvoke(invoke);
}

Data ContentExecutor::elementAsData(XERCESC_NS::DOMElement* element) {
	return _impl->elementAsData(element);
}

void ContentExecutor::raiseDoneEvent(XERCESC_NS::DOMElement* state, XERCESC_NS::DOMElement* doneData) {
	return _impl->raiseDoneEvent(state, doneData);
}

std::shared_ptr<ContentExecutorImpl> ContentExecutor::getImpl() const {
	return _impl;
}

}
