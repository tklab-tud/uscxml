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

#ifndef NAMESPACINGPARSER_H_BD6902F6
#define NAMESPACINGPARSER_H_BD6902F6

#include "uscxml/Common.h"
#include <iostream>
#include <XPath/XPath.hpp>
#include <DOM/io/Stream.hpp> // operator<< for nodes
#include <DOM/SAX2DOM/SAX2DOM.hpp>
#include <SAX/helpers/DefaultHandler.hpp>
#include <SAX/helpers/CatchErrorHandler.hpp>

namespace uscxml {

class ScriptEntityResolver : public Arabica::SAX::EntityResolver<std::string> {
	virtual InputSourceT resolveEntity(const std::string& publicId, const std::string& systemId) {
		Arabica::SAX::InputSource<std::string> is;
		return is;
	}
};

class USCXML_API NameSpacingParser : public Arabica::SAX2DOM::Parser<std::string> {
public:
	NameSpacingParser();
	NameSpacingParser(const NameSpacingParser& other) {}
	static NameSpacingParser fromFile(const std::string& file);
	static NameSpacingParser fromXML(const std::string& xml);
	static NameSpacingParser fromInputSource(Arabica::SAX::InputSource<std::string>& source);

	void startPrefixMapping(const std::string& prefix, const std::string& uri);

	std::map<std::string, std::string> nameSpace;

	virtual bool errorsReported() {
		return _errorHandler.errorsReported();
	}

	virtual const std::string& errors() {
		return _errorHandler.errors();
	}

private:
	Arabica::SAX::CatchErrorHandler<std::string> _errorHandler;
};

}


#endif /* end of include guard: NAMESPACINGPARSER_H_BD6902F6 */
