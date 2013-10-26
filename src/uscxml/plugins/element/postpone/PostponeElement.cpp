/**
 *  @file
 *  @author     2012-2013 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#include <boost/algorithm/string.hpp>

#include "PostponeElement.h"
#include "uscxml/plugins/invoker/http/HTTPServletInvoker.h"
#include <glog/logging.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool pluginConnect(pluma::Host& host) {
	host.add( new PostponeElementProvider() );
	return true;
}
#endif

boost::shared_ptr<ExecutableContentImpl> PostponeElement::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<PostponeElement> invoker = boost::shared_ptr<PostponeElement>(new PostponeElement());
	invoker->_interpreter = interpreter;
	return invoker;
}

void PostponeElement::enterElement(const Arabica::DOM::Node<std::string>& node) {
	if (!_interpreter->getDataModel()) {
		LOG(ERROR) << "Postpone element requires a datamodel";
		return;
	}

	// under which condition will we postpone the current event?
	if (HAS_ATTR(node, "cond")) {
		std::string cond = ATTR(node, "cond");
		try {
			if (!_interpreter->getDataModel().evalAsBool(cond))
				return;
		} catch (Event e) {
			LOG(ERROR) << "Syntax error in cond attribute of postpone element:" << std::endl << e << std::endl;
			return;
		}
	}

	// chaining causes the event to fire if the condition was true since postponing
	bool chained = false;
	if (HAS_ATTR(node, "chaining")) {
		chained = iequals(ATTR(node, "chaining"), "true");
	}

	// when will we refire the event?
	std::string until;
	try {
		if (HAS_ATTR(node, "untilexpr")) {
			until = _interpreter->getDataModel().evalAsString(ATTR(node, "untilexpr"));
		} else if (HAS_ATTR(node, "until")) {
			until = ATTR(node, "until");
		}
	} catch (Event e) {
		LOG(ERROR) << "Syntax error in postpone element untilexpr:" << std::endl << e << std::endl;
		return;
	}

	if (until.length() == 0) {
		LOG(ERROR) << "Postpone element requires until or untilexpr attribute ";
		return;
	}

//	LOG(INFO) << until;

#if 0
	std::string timeoutStr = "0s";
	try {
		if (HAS_ATTR(node, "timeoutexpr")) {
			timeoutStr = _interpreter->getDataModel().evalAsString(ATTR(node, "timeoutexpr"));
		} else if (HAS_ATTR(node, "timeout")) {
			timeoutStr = ATTR(node, "timeout");
		}
	} catch (Event e) {
		LOG(ERROR) << "Syntax error in postpone element timeoutexpr:" << std::endl << e << std::endl;
		return;
	}

	uint64_t timeout = 0;
	NumAttr timeoutAttr(timeoutStr);
	if (iequals(timeoutAttr.unit, "s")) {
		timeout = strTo<int>(timeoutAttr.value) * 1000;
	} else if (iequals(timeoutAttr.unit, "ms")) {
		timeout = strTo<int>(timeoutAttr.value);
	}
	if (timeout > 0) {
		timeout += tthread::chrono::system_clock::now();
	}
#endif
	Event currEvent = _interpreter->getCurrentEvent();
	Resubmitter::postpone(currEvent, until, 0, chained, _interpreter);
}

void PostponeElement::exitElement(const Arabica::DOM::Node<std::string>& node) {
}

void PostponeElement::Resubmitter::postpone(const Event& event, std::string until, uint64_t timeout, bool chained, InterpreterImpl* interpreter) {
	Resubmitter* resubmitter = getInstance(interpreter);
	resubmitter->_postponedEvents.push_back(Postponed(event, until, timeout, chained));
}

void PostponeElement::Resubmitter::onStableConfiguration(Interpreter interpreter) {
	std::list<Postponed>::iterator eventIter = _postponedEvents.begin();
	bool dispatched = false;
	while(eventIter != _postponedEvents.end()) {
		try {
//      LOG(INFO) << "Reevaluating: >> " << eventIter->first << " <<";
			if ((!dispatched || eventIter->chaining) && interpreter.getDataModel().evalAsBool(eventIter->until)) {
//        LOG(INFO) << "  -> is TRUE";
				eventIter->event.name += ".postponed";
				interpreter.receive(eventIter->event, true);
				_postponedEvents.erase(eventIter++);
				dispatched = true;
			}
//      LOG(INFO) << "  -> is FALSE";
		} catch (Event e) {
			LOG(ERROR) << "Syntax error while evaluating until attribute of postpone element:" << std::endl << e << std::endl;
			_postponedEvents.erase(eventIter++);
			continue;
		}
		eventIter++;
	}
//	LOG(ERROR) << _postponedEvents.size() << " Postponess remaining";

}

void PostponeElement::Resubmitter::afterCompletion(Interpreter interpreter) {
	tthread::lock_guard<tthread::recursive_mutex> lock(PostponeElement::Resubmitter::_accessLock);
	_instances.erase(interpreter);
	delete this; // committing suicide is ok if we are careful
}

std::map<Interpreter, PostponeElement::Resubmitter*> PostponeElement::Resubmitter::_instances;
tthread::recursive_mutex PostponeElement::Resubmitter::_accessLock;

PostponeElement::Resubmitter* PostponeElement::Resubmitter::getInstance(InterpreterImpl* interpreter) {
	tthread::lock_guard<tthread::recursive_mutex> lock(PostponeElement::Resubmitter::_accessLock);
	if (_instances.find(interpreter->shared_from_this()) == _instances.end()) {
		_instances[interpreter->shared_from_this()] = new Resubmitter(interpreter);
	}
	return _instances[interpreter->shared_from_this()];
}

}