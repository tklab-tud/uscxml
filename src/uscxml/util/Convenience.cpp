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

#include <inttypes.h>
#include <stdlib.h>
#include "Convenience.h"

namespace uscxml {

NumAttr::NumAttr(const std::string& str) {
    size_t valueStart = str.find_first_of("0123456789.");
    if (valueStart != std::string::npos) {
        size_t valueEnd = str.find_last_of("0123456789.");
        if (valueEnd != std::string::npos) {
            value = str.substr(valueStart, (valueEnd - valueStart) + 1);
            size_t unitStart = str.find_first_not_of(" \t", valueEnd + 1);
            if (unitStart != std::string::npos) {
                size_t unitEnd = str.find_last_of(" \t");
                if (unitEnd != std::string::npos && unitEnd > unitStart) {
                    unit = str.substr(unitStart, unitEnd - unitStart);
                } else {
                    unit = str.substr(unitStart, str.length() - unitStart);
                }
            }
        }
    }
}


bool isnan(double x) {
	return x != x;
}

bool isNumeric(const char* pszInput, int nNumberBase) {
	std::string base = ".-0123456789ABCDEF";
	std::string input = pszInput;
	return (input.find_first_not_of(base.substr(0, nNumberBase + 2)) == std::string::npos);
}

bool isInteger(const char* pszInput, int nNumberBase) {
	std::string base = "-0123456789ABCDEF";
	std::string input = pszInput;
	return (input.find_first_not_of(base.substr(0, nNumberBase + 1)) == std::string::npos);
}

bool iequals(const std::string& a, const std::string& b) {
	// this impementation beats boost::iequals 2700ms vs 2100ms for test-performance.scxml - we don't care for non-ascii yet
	unsigned int size = a.size();
	if (b.size() != size)
		return false;
	for (unsigned int i = 0; i < size; ++i)
		if (tolower(a[i]) != tolower(b[i]))
			return false;
	return true;
}

bool equals(const std::string& a, const std::string& b) {
	unsigned int size = a.size();
	if (b.size() != size)
		return false;
	for (unsigned int i = 0; i < size; ++i)
		if (a[i] != b[i])
			return false;
	return true;
}

bool stringIsTrue(const std::string& value) {
	return (iequals(value, "on") ||
	        iequals(value, "true") ||
	        iequals(value, "1") ||
	        iequals(value, "yes"));
}

bool envVarIsTrue(const char* name) {
	const char* value = getenv(name);
	if (value == NULL)
		return false;
	return stringIsTrue(value);
}

bool envVarIEquals(const char* name, const char* value) {
	const char* envVarValue = getenv(name);
	if (envVarValue == NULL)
		return false;
	return iequals(envVarValue, value);
}

std::string escape(const std::string& a) {
	std::stringstream b;
	// see http://en.cppreference.com/w/cpp/language/escape

	std::string::const_iterator it = a.begin();
	while (it != a.end()) {
		char c = *it++;
		switch (c) {
		case '\\':
			b << '\\' << '\\';
			break;
		case '\0':
			b << '\\' << '0';
			break;
		case '"':
			b << '\\' << '"';
			break;
		case '\a':
			b << '\\' << 'a';
			break;
		case '\b':
			b << '\\' << 'b';
			break;
		case '\f':
			b << '\\' << 'f';
			break;
		case '\n':
			b << '\\' << 'n';
			break;
		case '\r':
			b << '\\' << 'r';
			break;
		case '\t':
			b << '\\' << 't';
			break;
		case '\v':
			b << '\\' << 'v';
			break;
		default:
			b << c;
		}
	}

	return b.str();
}

std::string unescape(const std::string& a) {
	std::stringstream b;
	// see http://en.cppreference.com/w/cpp/language/escape

	std::string::const_iterator it = a.begin();
	while (it != a.end()) {
		char c = *it++;
		if (c == '\\' && it != a.end()) {
			switch (*it++) {
			case '\\':
				c = '\\';
				break;
			case '0':
				c = '\0';
				break;
			case '"':
				c = '"';
				break;
			case 'a':
				c = '\a';
				break;
			case 'b':
				c = '\b';
				break;
			case 'f':
				c = '\f';
				break;
			case 'n':
				c = '\n';
				break;
			case 'r':
				c = '\r';
				break;
			case 't':
				c = '\t';
				break;
			case 'v':
				c = '\v';
				break;
			}
		}
		b << c;
	}

	return b.str();
}

}
