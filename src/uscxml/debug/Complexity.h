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

#ifndef COMPLEXITY_H_F972C065
#define COMPLEXITY_H_F972C065

#include "uscxml/Common.h"              // for USCXML_API
#include "uscxml/Interpreter.h"

namespace uscxml {

class USCXML_API Complexity {
public:

	enum Variant {
		IGNORE_NOTHING      = 0x0000,
		IGNORE_HISTORY      = 0x0001,
		IGNORE_NESTED_DATA  = 0x0002,
		IGNORE_UNREACHABLE  = 0x0004,
	};

	Complexity() : value(0), nestedData(0) {}
	Complexity(uint64_t value) : value(value), nestedData(0) {}

	Complexity& operator+=(const Complexity& rhs) {
		value += rhs.value;
		nestedData += rhs.nestedData;
		history.insert(history.end(), rhs.history.begin(), rhs.history.end());
		return *this;
	}

	Complexity& operator*=(const Complexity& rhs) {
		value *= rhs.value;
		nestedData += rhs.nestedData;
		history.insert(history.end(), rhs.history.begin(), rhs.history.end());
		return *this;
	}

	static uint64_t stateMachineComplexity(const Interpreter& interpreter, Complexity::Variant variant = IGNORE_NOTHING) {
		return stateMachineComplexity(interpreter.getImpl().get());
	}
	static uint64_t stateMachineComplexity(InterpreterImpl* interpreter, Complexity::Variant variant = IGNORE_NOTHING);

	static std::list<std::set<Arabica::DOM::Element<std::string> > > getAllConfigurations(const Arabica::DOM::Element<std::string>& root);
	static std::map<size_t, size_t> getTransitionHistogramm(const Arabica::DOM::Element<std::string>& root);

protected:
	static Complexity calculateStateMachineComplexity(const Arabica::DOM::Element<std::string>& root, const Arabica::XPath::NodeSet<std::string>& reachable);

	uint64_t value;
	uint64_t nestedData;
	std::list<uint64_t> history;
};

inline Complexity::Variant operator | ( Complexity::Variant lhs, Complexity::Variant rhs ) {
	// Cast to int first otherwise we'll just end up recursing
	return static_cast< Complexity::Variant >( static_cast< int >( lhs ) | static_cast< int >( rhs ) );
}

}

#endif /* end of include guard: COMPLEXITY_H_F972C065 */
