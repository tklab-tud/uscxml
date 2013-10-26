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

namespace uscxml {
inline bool isnan(double x) {
	return x != x;
}

// see http://stackoverflow.com/questions/228005/alternative-to-itoa-for-converting-integer-to-string-c
template <typename T> std::string toStr(T tmp) {
	std::ostringstream out;
	out.precision(std::numeric_limits<double>::digits10 + 1);
	out << tmp;
	return out.str();
}

template <typename T> T strTo(std::string tmp) {
	T output;
	std::istringstream in(tmp);
	in >> output;
	return output;
}

inline bool isNumeric( const char* pszInput, int nNumberBase) {
	std::string base = ".-0123456789ABCDEF";
	std::string input = pszInput;
	return (input.find_first_not_of(base.substr(0, nNumberBase + 2)) == std::string::npos);
}

inline bool iequals(const std::string& a, const std::string& b) {
	unsigned int size = a.size();
	if (b.size() != size)
		return false;
	for (unsigned int i = 0; i < size; ++i)
		if (tolower(a[i]) != tolower(b[i]))
			return false;
	return true;
}

}


#endif /* end of include guard: CONVENIENCE_H_LU7GZ6CB */
