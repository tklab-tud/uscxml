/**
 *  @file
 *  @author     2012-2014 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
 *  @copyright  Simplified BSD
 *  @brief      Identifies some common problems with SCXML documents
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
#include <iostream>

// forward declare
namespace XERCESC_NS {
class DOMNode;
}

namespace uscxml {

class InterpreterImpl;

/**
 * Identify and report syntactic and semantic problems with a SCXML state-charts.
 * @see uscxml::Interpreter::validate()
 */
class USCXML_API InterpreterIssue {
public:
	enum IssueSeverity {
		USCXML_ISSUE_FATAL, ///< Interpreter can not process such a document
		USCXML_ISSUE_WARNING, ///< Document is questionable, but formally ok
		USCXML_ISSUE_INFO ///< Indicates a possible problem, but maybe perfectly ok
	};

	std::string xPath; ///< Where did the issue arise
	std::string message; ///< What is the issue
	XERCESC_NS::DOMNode* node; ///< The DOM node pertaining to the issue
	IssueSeverity severity; ///< Severity of the issue
	std::string specRef; ///< If applicable, the violated section from the standard

	/**
	 * Constructor is solely used to report issues at runtime.
	 */
	InterpreterIssue(const std::string& msg, XERCESC_NS::DOMNode* node, IssueSeverity severity, const std::string& specRef = "");

private:

	static std::list<InterpreterIssue> forInterpreter(InterpreterImpl* interpreter);
	friend class Interpreter;
};
USCXML_API std::ostream& operator<< (std::ostream& os, const InterpreterIssue& issue);

}

#endif /* end of include guard: INTERPRETERISSUE_H_962CB305 */
