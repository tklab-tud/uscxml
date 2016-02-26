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

#include "String.h"
#include <sstream>
#include <boost/algorithm/string.hpp>

namespace uscxml {

#define ISWHITESPACE(char) (isspace(char))

std::list<std::string> tokenize(const std::string& line, const char sep, bool trimWhiteSpace) {
	std::list<std::string> tokens;

	// appr. 3x faster than stringstream
	size_t start = 0;
	for (size_t i = 0; i < line.size(); i++) {
		if (line[i] == sep || (trimWhiteSpace && ISWHITESPACE(line[i]))) {
			if (i > 0 && start < i) {
				tokens.push_back(line.substr(start, i - start));
			}
			while(line[i] == sep || (trimWhiteSpace && ISWHITESPACE(line[i]))) {
				i++;    // skip multiple occurences of seperator and whitespaces
			}
			start = i;
		} else if (i + 1 == line.size()) {
			tokens.push_back(line.substr(start, i + 1 - start));
		}
	}

	return tokens;
}

std::string spaceNormalize(const std::string& text) {
	std::stringstream content;

#if 1
	// 195ms with test-performance-events.scml
	std::string seperator;

	size_t start = 0;
	for (size_t i = 0; i < text.size(); i++) {
		if (isspace(text[i])) {
			if (i > 0 && start < i) {
				content << seperator << text.substr(start, i - start);
				seperator = " ";
			}
			while(isspace(text[++i])); // skip whitespaces
			start = i;
		} else if (i + 1 == text.size()) {
			content << seperator << text.substr(start, i + 1 - start);
		}
	}
//	std::cerr << ">>" << content.str() << "<<" << std::endl;

#else

// 291ms with test-performance-events.scml
	std::istringstream iss(text);
	std::string seperator;
	do {
		std::string token;
		iss >> token;
		if (token.length() > 0) {
			content << seperator << token;
			seperator = " ";
		}
	} while (iss);

#endif
	return content.str();
}

// see: http://www.w3.org/TR/scxml/#EventDescriptors
bool nameMatch(const std::string& eventDescs, const std::string& eventName) {
#if 1
	if(eventDescs.length() == 0 || eventName.length() == 0)
		return false;

	// naive case of single descriptor and exact match
	if (boost::iequals(eventDescs, eventName))
		return true;

	size_t start = 0;
	std::string eventDesc;
	for (size_t i = 0; i < eventDescs.size(); i++) {
		if (isspace(eventDescs[i])) {
			if (i > 0 && start < i - 1) {
				eventDesc = eventDescs.substr(start, i - start);
			}
			while(isspace(eventDescs[++i])); // skip whitespaces
			start = i;
		} else if (i + 1 == eventDescs.size()) {
			eventDesc = eventDescs.substr(start, i + 1 - start);
		}

		if (eventDesc.size() > 0) {
			// remove optional trailing .* for CCXML compatibility
			if (eventDesc.find("*", eventDesc.size() - 1) != std::string::npos)
				eventDesc = eventDesc.substr(0, eventDesc.size() - 1);
			if (eventDesc.find(".", eventDesc.size() - 1) != std::string::npos)
				eventDesc = eventDesc.substr(0, eventDesc.size() - 1);

			// was eventDesc the * wildcard
			if (eventDesc.size() == 0)
				return true;

			// eventDesc has to be a real prefix of event now and therefore shorter
			if (eventDesc.size() > eventName.size())
				goto NEXT_DESC;

			// are they already equal?
			if (boost::iequals(eventDesc, eventName))
				return true;

			if (eventName.find(eventDesc) == 0) {
				if (eventName.find(".", eventDesc.size()) == eventDesc.size())
					return true;
			}
NEXT_DESC:
			eventDesc = "";
		}
	}
	return false;
#else
	const char* dPtr = eventDescs.c_str();
	const char* ePtr = eventName.c_str();
	while(*dPtr != 0) {

		if (*dPtr == '*' && *ePtr != 0) // something following
			return true;

		// descriptor differs from event name
		if (*dPtr != *ePtr) {
			// move to next descriptor
			while(*dPtr != ' ' && *dPtr != 0) {
				dPtr++;
			}
			if (*dPtr == 0)
				return false;
			dPtr++;
			ePtr = eventName.c_str();
		} else {
			// move both pointers one character
			dPtr++;
			ePtr++;

		}

		// descriptor is done, return match
		if (((*dPtr == 0 || *dPtr == ' ') && (*ePtr == 0 || *ePtr == ' ')) || // exact match, end of string
		        (*dPtr == ' ' && *ePtr == '.') || (*dPtr == 0 && *ePtr == '.')) // prefix match
			return true;
	}
	return false;
#endif
}


}