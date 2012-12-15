////////////////////////////////////////////////////////////
//
// Pluma - Plug-in Management Framework
// Copyright (C) 2010-2012 Gil Costa (gsaurus@gmail.com)
//
// This software is provided 'as-is', without any express or implied warranty.
// In no event will the authors be held liable for any damages arising from the use of this software.
//
// Permission is granted to anyone to use this software for any purpose,
// including commercial applications, and to alter it and redistribute it freely,
// subject to the following restrictions:
//
// 1. The origin of this software must not be misrepresented;
//    you must not claim that you wrote the original software.
//    If you use this software in a product, an acknowledgment
//    in the product documentation would be appreciated but is not required.
//
// 2. Altered source versions must be plainly marked as such,
//    and must not be misrepresented as being the original software.
//
// 3. This notice may not be removed or altered from any source distribution.
//
////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////
//
// Based on SFML configuration header
// SFML Config.hpp:
// http://www.sfml-dev.org/documentation/2.0/Config_8hpp-source.htm
//
// Acknowledgements to Simple and Fast Multimedia Library
// http://www.sfml-dev.org/
//
////////////////////////////////////////////////////////////


#ifndef PLUMA_CONFIG_HPP
#define PLUMA_CONFIG_HPP


////////////////////////////////////////////////////////////
// Identify the operating system
////////////////////////////////////////////////////////////
#if defined(WIN32) || defined(_WIN32) || defined(__WIN32__)

    // Windows
    #define PLUMA_SYS_WINDOWS
    #ifndef WIN32_LEAN_AND_MEAN
        #define WIN32_LEAN_AND_MEAN
    #endif
    #ifndef NOMINMAX
        #define NOMINMAX
    #endif

#elif defined(linux) || defined(__linux)

    // Linux
    #define PLUMA_SYS_LINUX

#elif defined(__APPLE__) || defined(MACOSX) || defined(macintosh) || defined(Macintosh)

    // MacOS
    #define PLUMA_SYS_MACOS

#elif defined(__FreeBSD__) || defined(__FreeBSD_kernel__)

    // FreeBSD
    #define PLUMA_SYS_FREEBSD

#else

    // Unsupported system
    #error This operating system is not supported by this library

#endif



////////////////////////////////////////////////////////////
// Define library file extension based on OS
////////////////////////////////////////////////////////////
#ifdef PLUMA_SYS_WINDOWS
     #define PLUMA_LIB_EXTENSION "dll"
#elif defined(PLUMA_SYS_MACOS)
     #define PLUMA_LIB_EXTENSION "dylib"
#elif defined(PLUMA_SYS_LINUX) || defined(PLUMA_SYS_FREEBSD)
     #define PLUMA_LIB_EXTENSION "so"
#else
   // unknown library file type
    #error Unknown library file extension for this operating system
#endif


////////////////////////////////////////////////////////////
// Define portable import / export macros
////////////////////////////////////////////////////////////
#if defined(PLUMA_SYS_WINDOWS)

    #ifndef PLUMA_STATIC

        // Windows platforms
        #ifdef PLUMA_EXPORTS

            // From DLL side, we must export
            #define PLUMA_API __declspec(dllexport)

        #else

            // From client application side, we must import
            #define PLUMA_API __declspec(dllimport)

        #endif

        // For Visual C++ compilers, we also need to turn off this annoying C4251 warning.
        // You can read lots ot different things about it, but the point is the code will
        // just work fine, and so the simplest way to get rid of this warning is to disable it
        #ifdef _MSC_VER

            #pragma warning(disable : 4251)

        #endif

    #else

        // No specific directive needed for static build
        #define PLUMA_API

    #endif

#else

    // Other platforms don't need to define anything
    #define PLUMA_API

#endif




#endif // PLUMA_CONFIG_HPP
