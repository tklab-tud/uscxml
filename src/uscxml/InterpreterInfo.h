/**
 *  @file
 *  @author     2012-2015 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#ifndef INTERPRETERINFO_H_CED68EFF
#define INTERPRETERINFO_H_CED68EFF

#include <iostream>

#include "uscxml/plugins/IOProcessor.h"
#include "uscxml/plugins/Invoker.h"

#include <XPath/XPath.hpp>
#include <DOM/Document.hpp>


namespace uscxml {

class USCXML_API NameSpaceInfo {
public:
	NameSpaceInfo() : nsContext(NULL) {
		init(std::map<std::string, std::string>());
	}

	NameSpaceInfo(const std::map<std::string, std::string>& nsInfo) : nsContext(NULL) {
		init(nsInfo);
	}

	NameSpaceInfo(const NameSpaceInfo& other) : nsContext(NULL) {
		init(other.nsInfo);
	}

	virtual ~NameSpaceInfo() {
		if (nsContext)
			delete nsContext;
	}

	NameSpaceInfo& operator=( const NameSpaceInfo& other ) {
		init(other.nsInfo);
		return *this;
	}

	void setPrefix(Arabica::DOM::Element<std::string> element) {
		if (nsURL.size() > 0)
			element.setPrefix(nsToPrefix[nsURL]);
	}

	void setPrefix(Arabica::DOM::Attr<std::string> attribute) {
		if (nsURL.size() > 0)
			attribute.setPrefix(nsToPrefix[nsURL]);
	}

	std::string getXMLPrefixForNS(const std::string& ns) const {
		if (nsToPrefix.find(ns) != nsToPrefix.end() && nsToPrefix.at(ns).size())
			return nsToPrefix.at(ns) + ":";
		return "";
	}

	const Arabica::XPath::StandardNamespaceContext<std::string>* getNSContext() {
		return nsContext;
	}

	std::string nsURL;         // ough to be "http://www.w3.org/2005/07/scxml" but maybe empty
	std::string xpathPrefix;   // prefix mapped for xpath, "scxml" is _xmlNSPrefix is empty but _nsURL set
	std::string xmlNSPrefix;   // the actual prefix for elements in the xml file
	std::map<std::string, std::string> nsToPrefix;  // prefixes for a given namespace
	std::map<std::string, std::string> nsInfo;      // all xmlns mappings

private:
	Arabica::XPath::StandardNamespaceContext<std::string>* nsContext;

	void init(const std::map<std::string, std::string>& nsInfo);
};

class USCXML_API InterpreterInfo {
public:
	virtual NameSpaceInfo getNameSpaceInfo() const = 0;
	virtual const std::string& getName() = 0;
	virtual const std::string& getSessionId() = 0;
	virtual const std::map<std::string, IOProcessor>& getIOProcessors() = 0;
	virtual bool isInState(const std::string& stateId) = 0;
	virtual Arabica::DOM::Document<std::string> getDocument() const = 0;
	virtual const std::map<std::string, Invoker>& getInvokers() = 0;
};

}

#endif /* end of include guard: INTERPRETERINFO_H_CED68EFF */
