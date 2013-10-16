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
#include <winsock2.h>
// see http://stackoverflow.com/questions/1372480/c-redefinition-header-files
#define _WINSOCKAPI_    // stops windows.h including winsock.h
#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#undef WIN32_LEAN_AND_MEAN
#else
#include <sys/socket.h>
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

// dll interface
#pragma warning (disable : 4251)

#endif


#endif /* end of include guard: COMMON_H_YZ3CIYP */
