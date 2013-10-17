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

#include <uscxml/Common.h>
#include "NameSpacingParser.h"
#include <glog/logging.h>
#include <SAX/helpers/InputSourceResolver.hpp>

namespace uscxml {

NameSpacingParser NameSpacingParser::fromXML(const std::string& xml) {
	std::stringstream* ss = new std::stringstream();
	(*ss) << xml;
	// we need an auto_ptr for arabica to assume ownership
	std::auto_ptr<std::istream> ssPtr(ss);
	Arabica::SAX::InputSource<std::string> inputSource;
	inputSource.setByteStream(ssPtr);
	return fromInputSource(inputSource);
}

NameSpacingParser NameSpacingParser::fromInputSource(Arabica::SAX::InputSource<std::string>& source) {
	NameSpacingParser parser;
	if(!parser.parse(source) || !parser.getDocument().hasChildNodes()) {
		if(parser._errorHandler.errorsReported()) {
			LOG(ERROR) << "could not parse input:";
			LOG(ERROR) << parser._errorHandler.errors() << std::endl;
		} else {
			Arabica::SAX::InputSourceResolver resolver(source, Arabica::default_string_adaptor<std::string>());
			if (!resolver.resolve()) {
				LOG(ERROR) << source.getSystemId() << ": no such file";
			}
		}
	}
	return parser;
}

NameSpacingParser::NameSpacingParser() {
	setErrorHandler(_errorHandler);
}

void NameSpacingParser::startPrefixMapping(const std::string& prefix, const std::string& uri) {
	nameSpace.insert(std::make_pair(uri, prefix));
}

}