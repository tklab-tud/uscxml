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

#include "uscxml/transform/ChartToFSM.h"
#include "uscxml/transform/FSMToPromela.h"
#include <DOM/io/Stream.hpp>
#include <iostream>
#include "uscxml/UUID.h"
#include <math.h>

namespace uscxml {

using namespace Arabica::DOM;
using namespace Arabica::XPath;

void FSMToPromela::writeProgram(std::ostream& stream,
																const Arabica::DOM::Document<std::string>& doc,
																const std::map<std::string, std::string>& namespaceInfo) {

}

FSMToPromela::FSMToPromela(const Arabica::DOM::Document<std::string>& doc,
													 const std::map<std::string, std::string>& namespaceInfo) {
		
	std::map<std::string, std::string>::const_iterator nsIter = namespaceInfo.begin();
	while(nsIter != namespaceInfo.end()) {
		std::string uri = nsIter->first;
		std::string prefix = nsIter->second;
		if (iequals(uri, "http://www.w3.org/2005/07/scxml")) {
			_nsURL = uri;
			if (prefix.size() == 0) {
				_xpathPrefix = "scxml:";
				_nsContext.addNamespaceDeclaration(uri, "scxml");
				_nsToPrefix[uri] = "scxml";
			} else {
				_xpathPrefix = prefix + ":";
				_xmlNSPrefix = _xpathPrefix;
				_nsContext.addNamespaceDeclaration(uri, prefix);
				_nsToPrefix[uri] = prefix;
			}
		} else {
			_nsContext.addNamespaceDeclaration(uri, prefix);
			_nsToPrefix[uri] = prefix;
		}
		nsIter++;
	}
	_xpath.setNamespaceContext(_nsContext);

	_document = doc;
	NodeList<std::string> scxmls = _document.getElementsByTagNameNS(_nsURL, "scxml");
	if (scxmls.getLength() > 0) {
		_scxml = (Arabica::DOM::Element<std::string>)scxmls.item(0);
	}
}

void FSMToPromela::writeProgram(std::ostream& stream) {
	stream << "foo";
}

}