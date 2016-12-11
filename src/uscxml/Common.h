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

#ifndef COMMON_H_YZ3CIYP
#define COMMON_H_YZ3CIYP

#define XERCESC_NS xercesc_3_1

#ifndef _MSC_VER
#define ELPP_STACKTRACE_ON_CRASH 1
#endif

#if __cplusplus >= 201402L
#define DEPRECATED [[deprecated]]
#elif defined(__GNUC__)
#define DEPRECATED __attribute__((deprecated))
#elif defined(_MSC_VER)
#define DEPRECATED __declspec(deprecated)
#else
#pragma message("WARNING: You need to implement DEPRECATED for this compiler")
#define DEPRECATED(alternative)
#endif

#if defined(_WIN32) && !defined(USCXML_STATIC)
#	ifdef USCXML_EXPORT
#		define USCXML_API __declspec(dllexport)
#	else
#		define USCXML_API __declspec(dllimport)
#	endif
#else
#	define USCXML_API
#endif

#ifdef _WIN32
#define NOMINMAX

typedef unsigned __int32  uint32_t;

// see http://stackoverflow.com/questions/1372480/c-redefinition-header-files
#define _WINSOCKAPI_    // stops windows.h including winsock.h
#include <winsock2.h>
#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#undef WIN32_LEAN_AND_MEAN
#else
#include <sys/socket.h>
#endif

/**
   The usual operators as required for the PIMPL pattern.
 */
#define PIMPL_OPERATORS(type) \
type() : _impl() { } \
type(const std::shared_ptr<type##Impl> impl) : _impl(impl) { }\
type(const type& other) : _impl(other._impl) { }\
virtual ~type() { };\
\
operator bool()                    const     {\
    return !!_impl;\
}\
bool operator< (const type& other) const     {\
    return _impl < other._impl;\
}\
bool operator==(const type& other) const     {\
    return _impl == other._impl;\
}\
bool operator!=(const type& other) const     {\
    return _impl != other._impl;\
}\
type& operator= (const type& other)          {\
    _impl = other._impl;\
    return *this;\
}

#define PIMPL_OPERATORS_INHERIT(type, base) \
type() : _impl() {}\
type(std::shared_ptr<type##Impl> const impl);\
type(const type& other);\
virtual ~type() {};\
\
operator bool()                    const     {\
    return !!_impl;\
}\
bool operator< (const type& other) const     {\
    return _impl < other._impl;\
}\
bool operator==(const type& other) const     {\
    return _impl == other._impl;\
}\
bool operator!=(const type& other) const     {\
    return _impl != other._impl;\
}\
type& operator= (const type& other);


#define PIMPL_OPERATORS_INHERIT_IMPL(type, base) \
type::type(std::shared_ptr<type##Impl> const impl) : base(impl), _impl(impl) { }\
type::type(const type& other) : base(other._impl), _impl(other._impl) { }\
type& type::operator= (const type& other)   {\
    _impl = other._impl;\
    base::_impl = _impl;\
    return *this;\
}


#if defined(_WIN32)
inline int setenv(const char *name, const char *value, int overwrite) {
	int errcode = 0;
	if(!overwrite) {
		size_t envsize = 0;
		errcode = getenv_s(&envsize, NULL, 0, name);
		if(errcode || envsize) return errcode;
	}
	return _putenv_s(name, value);
}
#endif

#define _USE_MATH_DEFINES
#include <cmath>

#if defined(_MSC_VER)
// disable signed / unsigned comparison warnings
#pragma warning (disable : 4018)
// possible loss of data
#pragma warning (disable : 4244)
#pragma warning (disable : 4267)
// 'this' : used in base member initializer list
#pragma warning (disable : 4355)

// is thrown alot in arabica headers
#pragma warning (disable : 4240)
#pragma warning (disable : 4250)
#pragma warning (disable : 4661)

// dll interface
#pragma warning (disable : 4251)

#endif


#endif /* end of include guard: COMMON_H_YZ3CIYP */
