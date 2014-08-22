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

#ifndef INTERPRETERISSUE_H_962CB305
#define INTERPRETERISSUE_H_962CB305

#include "uscxml/Common.h"
#include <list>
#include <DOM/Node.hpp>

namespace uscxml {

class InterpreterImpl;
	
class USCXML_API InterpreterIssue {
public:
	enum IssueSeverity {
		USCXML_ISSUE_FATAL,
		USCXML_ISSUE_WARNING,
		USCXML_ISSUE_INFO
	};
	
	InterpreterIssue(const std::string& msg, Arabica::DOM::Node<std::string> node, IssueSeverity severity);

	std::string xPath;
	std::string message;
	Arabica::DOM::Node<std::string> node;
	IssueSeverity severity;
	
private:
	static std::list<InterpreterIssue> forInterpreter(InterpreterImpl* interpreter);
	friend class InterpreterImpl;
};
USCXML_API std::ostream& operator<< (std::ostream& os, const InterpreterIssue& issue);

}

#endif /* end of include guard: INTERPRETERISSUE_H_962CB305 */
