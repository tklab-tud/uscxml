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

#include "uscxml/Message.h"

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
	
	Breakpoint() {}
	Breakpoint(const Data& data);
	
	// would we match the given breakpoint as well?
	bool matches(const Breakpoint& other) const;
	
	bool isValid();
	
	Data toData() const;
	
	bool operator<(const Breakpoint& other) const {
		return (origData < other.origData);
	}
	
	When when;
	Subject subject;
	Action action;

	std::string invokeId;
	std::string invokeType;

	std::string eventName;
	
	std::string stateId;
	std::string transSource;
	std::string transTarget;
	
	std::string condition;
	Data origData;
};

}



#endif /* end of include guard: BREAKPOINT_H_VR7K7T1X */
