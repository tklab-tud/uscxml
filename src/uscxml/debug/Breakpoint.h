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

#ifndef BREAKPOINT_H_VR7K7T1X
#define BREAKPOINT_H_VR7K7T1X

#include <string>                       // for string
#include "uscxml/Common.h"              // for USCXML_API
#include "uscxml/Interpreter.h"
//#include "DOM/Element.hpp"              // for Element
#include "uscxml/messages/Data.h"       // for Data

// forward declare
namespace XERCESC_NS {
class DOMElement;
}

namespace uscxml {

class USCXML_API Breakpoint {
public:

	enum When {
		UNDEF_WHEN, AFTER, BEFORE, ON
	};

	enum Subject {
		UNDEF_SUBJECT, STATE, TRANSITION, STABLE, MICROSTEP, EVENT, INVOKER, EXECUTABLE
	};

	enum Action {
		UNDEF_ACTION, ENTER, EXIT, INVOKE, UNINVOKE
	};

	Breakpoint() {
		subject = UNDEF_SUBJECT;
		when    = UNDEF_WHEN;
		action  = UNDEF_ACTION;
		enabled = true;
	}
	Breakpoint(const Data& data);

	// would we match the given breakpoint as well?
	bool matches(Interpreter interpreter, const Breakpoint& other) const;

	Data toData() const;

	bool operator<(const Breakpoint& other) const {
		return (toData() < other.toData());
	}

	operator bool() {
		return (subject != UNDEF_SUBJECT ||
		        when    != UNDEF_WHEN ||
		        action  != UNDEF_ACTION);
	}

	mutable bool enabled;

	When when;
	Subject subject;
	Action action;

	const XERCESC_NS::DOMElement* element = NULL;

	std::string invokeId;
	std::string invokeType;

	std::string eventName;

	std::string executableName;
	std::string executableXPath;

	std::string stateId;
	std::string transSourceId;
	std::string transTargetId;

	std::string condition;
};

}



#endif /* end of include guard: BREAKPOINT_H_VR7K7T1X */
