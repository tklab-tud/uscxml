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
	outSS.imbue(std::locale("C"));
	outSS << tmp;
	return outSS.str();
}

template <typename T> T strTo(std::string tmp) {
	T output;
	std::istringstream in(tmp);
	in.imbue(std::locale("C"));
	in >> output;
	return output;
}

class USCXML_API NumAttr {
public:
	NumAttr(const std::string& str);
	std::string value;
	std::string unit;
};

bool USCXML_API isNumeric(const char* pszInput, int nNumberBase);
bool USCXML_API isInteger( const char* pszInput, int nNumberBase);
bool USCXML_API iequals(const std::string& a, const std::string& b);
bool USCXML_API equals(const std::string& a, const std::string& b);
bool USCXML_API stringIsTrue(const std::string& value);
bool USCXML_API envVarIsTrue(const char* name);
bool USCXML_API envVarIEquals(const char* name, const char* value);

std::string USCXML_API escape(const std::string& a);
std::string USCXML_API unescape(const std::string& a);

}
#endif /* end of include guard: CONVENIENCE_H_LU7GZ6CB */
