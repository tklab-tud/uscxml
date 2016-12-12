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

#ifndef CONVENIENCE_H_LU7GZ6CB
#define CONVENIENCE_H_LU7GZ6CB

#include "uscxml/Common.h"
#include <string>
#include <limits>
#include <sstream>

namespace uscxml {
inline bool isnan(double x);

// see http://stackoverflow.com/questions/228005/alternative-to-itoa-for-converting-integer-to-string-c
template <typename T> std::string toStr(T tmp) {
	std::ostringstream outSS;
	outSS.precision(std::numeric_limits<double>::digits10 + 1);
	outSS << tmp;
	return outSS.str();
}

template <typename T> T strTo(std::string tmp) {
	T output;
	std::istringstream in(tmp);
	in >> output;
	return output;
}

class USCXML_API NumAttr {
public:
    NumAttr(const std::string& str);
	std::string value;
	std::string unit;
};

bool isNumeric(const char* pszInput, int nNumberBase);
bool isInteger( const char* pszInput, int nNumberBase);
bool iequals(const std::string& a, const std::string& b);
bool equals(const std::string& a, const std::string& b);
bool stringIsTrue(const std::string& value);
bool envVarIsTrue(const char* name);
bool envVarIEquals(const char* name, const char* value);

std::string escape(const std::string& a);
std::string unescape(const std::string& a);

}
#endif /* end of include guard: CONVENIENCE_H_LU7GZ6CB */
