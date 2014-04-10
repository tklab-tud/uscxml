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

#ifndef FSMTOPROMELA_H_RP48RFDJ
#define FSMTOPROMELA_H_RP48RFDJ

#include "uscxml/DOMUtils.h"
#include <DOM/Document.hpp>
#include <DOM/Node.hpp>
#include <XPath/XPath.hpp>
#include <ostream>

namespace uscxml {
	
class FSMToPromela {
public:
	static void writeProgram(std::ostream& stream,
													 const Arabica::DOM::Document<std::string>& doc,
													 const std::map<std::string, std::string>& namespaceInfo);
protected:
	FSMToPromela(const Arabica::DOM::Document<std::string>& doc,
							 const std::map<std::string, std::string>& namespaceInfo);
	
	void writeProgram(std::ostream& stream);
	
	Arabica::DOM::Document<std::string> _document;
	Arabica::DOM::Node<std::string> _scxml;
	
	Arabica::XPath::XPath<std::string> _xpath;
	Arabica::XPath::StandardNamespaceContext<std::string> _nsContext;
	std::string _xmlNSPrefix; // the actual prefix for elements in the xml file
	std::string _xpathPrefix; // prefix mapped for xpath, "scxml" is _xmlNSPrefix is empty but _nsURL set
	std::string _nsURL;       // ough to be "http://www.w3.org/2005/07/scxml"
	std::map<std::string, std::string> _nsToPrefix;
	std::map<std::string, std::string> _nameSpaceInfo;

};
	
}

#endif /* end of include guard: FSMTOPROMELA_H_RP48RFDJ */
