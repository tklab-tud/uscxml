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
	
}


#endif /* end of include guard: CONVENIENCE_H_LU7GZ6CB */
