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

#include "uscxml/debug/Breakpoint.h"
#include "uscxml/Interpreter.h"
#include "uscxml/interpreter/InterpreterImpl.h"
#include "uscxml/util/DOM.h"
#include "uscxml/util/String.h"

namespace uscxml {

Breakpoint::Breakpoint(const Data& data) {
	enabled = true;
	subject = UNDEF_SUBJECT;
	when    = UNDEF_WHEN;
	action  = UNDEF_ACTION;

	if (data.hasKey("when")) {
		if (false) {
		} else if (data.at("when").atom == "before") {
			when = BEFORE;
		} else if (data.at("when").atom == "after") {
			when = AFTER;
		} else if (data.at("when").atom == "on") {
			when = ON;
		}
	}

	if (data.hasKey("action")) {
		if (false) {
		} else if (data.at("action").atom == "enter") {
			action = ENTER;
		} else if (data.at("action").atom == "exit") {
			action = EXIT;
		} else if (data.at("action").atom == "invoke") {
			action = INVOKE;
		} else if (data.at("action").atom == "cancel") {
			action = UNINVOKE;
		}
	}

	if (data.hasKey("subject")) {
		if (false) {
		} else if (data.at("subject").atom == "state") {
			subject = STATE;
		} else if (data.at("subject").atom == "transition") {
			subject = TRANSITION;
		} else if (data.at("subject").atom == "stable") {
			subject = STABLE;
		} else if (data.at("subject").atom == "microstep") {
			subject = MICROSTEP;
		} else if (data.at("subject").atom == "event") {
			subject = EVENT;
		} else if (data.at("subject").atom == "invoker") {
			subject = INVOKER;
		} else if (data.at("subject").atom == "executable") {
			subject = EXECUTABLE;
		}
	}

	if (data.hasKey("condition"))
		condition = data.at("condition").atom;

	if (data.hasKey("invokeId"))
		invokeId = data.at("invokeId").atom;

	if (data.hasKey("invokeType"))
		invokeType = data.at("invokeType").atom;

	if (data.hasKey("eventName"))
		eventName = data.at("eventName").atom;

	if (data.hasKey("execName"))
		executableName = data.at("execName").atom;

	if (data.hasKey("execXPath"))
		executableXPath = data.at("execXPath").atom;

	if (data.hasKey("stateId"))
		stateId = data.at("stateId").atom;

	if (data.hasKey("source"))
		transSourceId = data.at("source").atom;

	if (data.hasKey("target"))
		transTargetId = data.at("target").atom;

}

Data Breakpoint::toData() const {
	Data data;

	switch (subject) {
	case STATE:
		data.compound["subject"] = Data("state", Data::VERBATIM);
		break;
	case TRANSITION:
		data.compound["subject"] = Data("transition", Data::VERBATIM);
		break;
	case STABLE:
		data.compound["subject"] = Data("stable", Data::VERBATIM);
		break;
	case MICROSTEP:
		data.compound["subject"] = Data("microstep", Data::VERBATIM);
		break;
	case EVENT:
		data.compound["subject"] = Data("event", Data::VERBATIM);
		break;
	case INVOKER:
		data.compound["subject"] = Data("invoker", Data::VERBATIM);
		break;
	case EXECUTABLE:
		data.compound["subject"] = Data("executable", Data::VERBATIM);
		break;
	default:
		break;
	}

	switch (when) {
	case AFTER:
		data.compound["when"] = Data("after", Data::VERBATIM);
		break;
	case BEFORE:
		data.compound["when"] = Data("before", Data::VERBATIM);
		break;
	case ON:
		data.compound["when"] = Data("on", Data::VERBATIM);
		break;
	default:
		break;
	}

	switch (action) {
	case ENTER:
		data.compound["action"] = Data("enter", Data::VERBATIM);
		break;
	case EXIT:
		data.compound["action"] = Data("exit", Data::VERBATIM);
		break;
	case INVOKE:
		data.compound["action"] = Data("invoke", Data::VERBATIM);
		break;
	case UNINVOKE:
		data.compound["action"] = Data("cancel", Data::VERBATIM);
		break;
	default:
		break;
	}

	if (invokeId.length() > 0)
		data.compound["invokeId"] = Data(invokeId, Data::VERBATIM);

	if (invokeType.length() > 0)
		data.compound["invokeType"] = Data(invokeType, Data::VERBATIM);

	if (eventName.length() > 0)
		data.compound["eventName"] = Data(eventName, Data::VERBATIM);

	if (executableName.length() > 0)
		data.compound["execName"] = Data(executableName, Data::VERBATIM);

	if (executableXPath.length() > 0) {
		data.compound["execXPath"] = Data(executableXPath, Data::VERBATIM);
	}

	if (element)
		data.compound["xpath"] = Data(DOMUtils::xPathForNode(element, "*"), Data::VERBATIM);

	if (stateId.length() > 0)
		data.compound["stateId"] = Data(stateId, Data::VERBATIM);

	if (transSourceId.length() > 0)
		data.compound["source"] = Data(transSourceId, Data::VERBATIM);

	if (transTargetId.length() > 0)
		data.compound["target"] = Data(transTargetId, Data::VERBATIM);

	if (condition.length() > 0)
		data.compound["condition"] = Data(condition, Data::VERBATIM);

	return data;
}

bool Breakpoint::matches(Interpreter interpreter, const Breakpoint& other) const {
	// would we match the given breakpoint?

	if (subject != UNDEF_SUBJECT &&
	        other.subject != subject)
		return false; // subject does not match

	if (when != UNDEF_WHEN &&
	        other.when != when)
		return false; // time does not match

	if (action != UNDEF_ACTION &&
	        other.action != action)
		return false; // action does not match

	// when we have a qualifier it has to match
	if(invokeId.length() > 0 && invokeId != other.invokeId) {
		return false;
	}

	if(invokeType.length() > 0 && invokeType != other.invokeType) {
		return false;
	}

	if(stateId.length() > 0 && stateId != other.stateId) {
		return false;
	}

	if(eventName.length() > 0 && !nameMatch(eventName, other.eventName)) {
		return false;
	}

	if(executableName.length() > 0 && executableName != other.executableName) {
		return false;
	}

#if 0
	if(executableXPath.length()) {
		Arabica::XPath::NodeSet<std::string> nodes;
		try {
			nodes = interpreter.getNodeSetForXPath(executableXPath);
		} catch (...) {
			return false;
		}
		return InterpreterImpl::isMember(other.element, nodes);
	}
#endif

	if(transSourceId.length() > 0 && transSourceId != other.transSourceId) {
		return false;
	}

	if(transTargetId.length() > 0 && transTargetId != other.transTargetId) {
		return false;
	}

	if (condition.length() > 0) {
		try {
			interpreter.getImpl()->isTrue(condition);
		} catch (...) {
			return false;
		}
	}

	return true;
}

}