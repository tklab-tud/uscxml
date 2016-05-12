# travis build slaves ony feature 2.8.7 - let's hope it's sufficient
cmake_minimum_required(VERSION 2.8.7 FATAL_ERROR)

# build type has to be set before the project definition
SET(BUILD_TYPE_HELP "Choose the type of build, options are: None(CMAKE_CXX_FLAGS or CMAKE_C_FLAGS used) Debug, Release, RelWithDebInfo, MinSizeRel.")
IF(DEFINED CMAKE_BUILD_TYPE)
   SET(CMAKE_BUILD_TYPE ${CMAKE_BUILD_TYPE} CACHE STRING ${BUILD_TYPE_HELP})
ELSE()
   SET(CMAKE_BUILD_TYPE Release CACHE STRING ${BUILD_TYPE_HELP})
ENDIF()

PROJECT(uscxml)

#################################################
# General Setup
#################################################

# specify USCXML version
SET(USCXML_VERSION_MAJOR "2")
SET(USCXML_VERSION_MINOR "0")
SET(USCXML_VERSION_PATCH "0")
SET(USCXML_VERSION ${USCXML_VERSION_MAJOR}.${USCXML_VERSION_MINOR}.${USCXML_VERSION_PATCH})

set(CMAKE_MACOSX_RPATH 1)

# where do libraries and binaries go
set (CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)
set (CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set (CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)

# where to find more cmake scripts
set(CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/contrib/cmake)
include("${CMAKE_MODULE_PATH}/USCXMLMacros.cmake")

# setup header include paths
include_directories(src)
include_directories(contrib/src)
include_directories(${CMAKE_BINARY_DIR})
include_directories(${PROJECT_SOURCE_DIR}/contrib/src/jsmn)
include_directories(${PROJECT_SOURCE_DIR}/contrib/src/evws)
if (WIN32)
	include_directories(${PROJECT_SOURCE_DIR}/contrib/src/getopt)
	include_directories(${PROJECT_SOURCE_DIR}/contrib/src/inttypes)
endif()

# various options
# OPTION(BUILD_MINIMAL "Build only features mandated by specification" OFF)
# OPTION(BUILD_DM_ECMA "Build with ECMAScript datamodel" ON)
# OPTION(BUILD_DM_XPATH "Build with XPath datamodel" OFF)
# OPTION(BUILD_DM_PROLOG "Build with Prolog datamodel" OFF)
# OPTION(BUILD_DM_PROMELA "Build with Promela datamodel" OFF)
# OPTION(BUILD_DM_LUA "Build with Lua datamodel" OFF)


################################
# Compiler Features and Flags

# Check for C++11 support
# message("Your C++ compiler supports these C++ features:")
# foreach(i ${CMAKE_CXX_COMPILE_FEATURES})
#   message("${i}")
# endforeach()

# http://stackoverflow.com/a/25836953/990120
include(CheckCXXCompilerFlag)
CHECK_CXX_COMPILER_FLAG("-std=c++11" COMPILER_SUPPORTS_CXX11_FLAG)
CHECK_CXX_COMPILER_FLAG("-std=c++0x" COMPILER_SUPPORTS_CXX0X_FLAG)
if(COMPILER_SUPPORTS_CXX11_FLAG)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11")
elseif(COMPILER_SUPPORTS_CXX0X_FLAG)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++0x")
endif()

if(${CMAKE_CXX_COMPILER_ID} STREQUAL GNU)

elseif (${CMAKE_CXX_COMPILER_ID} STREQUAL Clang)
	
elseif (${CMAKE_CXX_COMPILER_ID} STREQUAL MSVC)
	add_definitions("-D_SCL_SECURE_NO_WARNINGS")
	add_definitions("-D_CRT_SECURE_NO_WARNINGS")
else()
	message(STATUS "Unknown compiler: ${CMAKE_CXX_COMPILER_ID}")
endif()
set(CMAKE_COMPILER_STRING "${CMAKE_CXX_COMPILER_ID} ${CMAKE_CXX_COMPILER_VERSION}")

# https://cmake.org/Bug/view.php?id=15361
set(CMAKE_REQUIRED_DEFINITIONS ${CMAKE_CXX11_STANDARD_COMPILE_OPTION})

include(CheckCXXSourceCompiles)
check_cxx_source_compiles("
	#include <thread>
	int main(){ return 0; }
" CXX_HAS_THREADS)
check_cxx_source_compiles("
	#include <memory>
	int main(){ std::shared_ptr<void> foo(NULL); return 0; }
" CXX_HAS_SHARED_PTR)
check_cxx_source_compiles("
	int main(){ int foo[10]; auto i = foo[0]; }
" CXX_HAS_AUTOTYPE)
check_cxx_source_compiles("
	int main(){ []{}(); }
" CXX_HAS_LAMBDAS)

set(CXX_MISSING_FEATURES "")
if (NOT CXX_HAS_LAMBDAS)
	set(CXX_MISSING_FEATURES "${CXX_MISSING_FEATURES} lambdas")
endif()
if(NOT CXX_HAS_THREADS)
	set(CXX_MISSING_FEATURES "${CXX_MISSING_FEATURES} threads")
endif()
if(NOT CXX_HAS_AUTOTYPE)
	set(CXX_MISSING_FEATURES "${CXX_MISSING_FEATURES} autotype")
endif()
if(NOT CXX_HAS_SHARED_PTR)
	set(CXX_MISSING_FEATURES "${CXX_MISSING_FEATURES} shared_ptr")
endif()

if (CXX_MISSING_FEATURES)
	message(FATAL_ERROR "Compiler is missing required C++11 features: ${CXX_MISSING_FEATURES}")
endif()

if (CMAKE_CROSSCOMPILING OR WIN32)
	OPTION(BUILD_SHARED_LIBS "Build shared libraries" OFF)
else()
	OPTION(BUILD_SHARED_LIBS "Build shared libraries" ON)
endif()

# built shared or static libraries?
if(BUILD_SHARED_LIBS)
	add_definitions("-DUSCXML_EXPORT")
else()
	add_definitions("-DUSCXML_STATIC")
endif()


#################################################
# Dependent Libraries
#################################################


################################
# Required
set(USCXML_PREREQS)

# CURL
find_package(CURL)
if (CURL_FOUND)
	include_directories(${CURL_INCLUDE_DIRS})
	list (APPEND USCXML_CORE_LIBS ${CURL_LIBRARIES})

	include(CheckCXXSourceCompiles)
	set(CMAKE_REQUIRED_INCLUDES ${CURL_INCLUDE_DIRS})
	set(CMAKE_REQUIRED_LIBRARIES ${CURL_LIBRARIES})
	check_cxx_source_compiles("
		#include <curl/curl.h>
		int main(){ return CURLOPT_MAIL_RCPT; }
	" CURL_HAS_SMTP)
else()
	message(STATUS "--> will download and compile")
	include("${CMAKE_MODULE_PATH}/BuildLibCURL.cmake")
	if (LIBCURL_BUILT)
		include_directories(${LIBCURL_INCLUDE_DIR})
		list (APPEND USCXML_CORE_LIBS ${LIBCURL_LIBRARY})
		list (APPEND USCXML_PREREQS libcurl)
		set(CURL_HAS_SMTP ON)
	else()
		message(FATAL_ERROR "Could neither find nor build CURL")
	endif()
endif()


# XercesC
CheckHasModule(XercesC)
if (HAS_MODULE_XercesC)
	find_package(XercesC)
else()
	message(STATUS "Could NOT find XercesC (your CMake distribution does not include the FindXercesC module)")
endif()
if (XercesC_FOUND)
	include_directories(${XercesC_INCLUDE_DIRS})
	list (APPEND USCXML_CORE_LIBS ${XercesC_LIBRARIES})
else()
	message(STATUS "--> will download and compile")
	include("${CMAKE_MODULE_PATH}/BuildXercesC.cmake")
	if (XercesC_BUILT)
		include_directories(${XercesC_INCLUDE_DIRS})
		list (APPEND USCXML_CORE_LIBS ${XercesC_LIBRARIES})
		list (APPEND USCXML_PREREQS xerces-c)
	else()
		message(FATAL_ERROR "Could neither find nor build XercesC")
	endif()
endif()

# LibEvent
find_package(LibEvent)
if (LIBEVENT_FOUND)
	include_directories(${LIBEVENT_INCLUDE_DIR})
	list (APPEND USCXML_CORE_LIBS ${LIBEVENT_LIBRARIES})
else()
	message(STATUS "--> will download and compile")
	include("${CMAKE_MODULE_PATH}/BuildLibEvent.cmake")
	if (LIBEVENT_BUILT)
		include_directories(${LIBEVENT_INCLUDE_DIR})
		list (APPEND USCXML_CORE_LIBS ${LIBEVENT_LIBRARIES})
		list (APPEND USCXML_PREREQS libevent)
	else()
		message(FATAL_ERROR "Could neither find nor build libevent")
	endif()
endif()

if (UNIX)
	list (APPEND USCXML_CORE_LIBS "pthread")
endif()

# uriparser
include("${CMAKE_MODULE_PATH}/BuildURIParser.cmake")
message(STATUS "Did not look for UriParser")
message(STATUS "--> will download and compile")
if (URIPARSER_BUILT)
	include_directories(${URIPARSER_INCLUDE_DIR})
	list (APPEND USCXML_CORE_LIBS ${URIPARSER_LIBRARY})
	list (APPEND USCXML_PREREQS uriparser)
else()
	message(FATAL_ERROR "Could not build uriparser")
endif()


################################
# Optional

# JavaScriptCore
find_package(JSC)
if (JSC_FOUND)
	set(ECMA_FOUND ON)
	if (NOT APPLE)
		include_directories(${JSC_INCLUDE_DIR})
	endif()
	list (APPEND USCXML_OPT_LIBS ${JSC_LIBRARY})
endif()

find_package(V8)
if (V8_FOUND)
	set(ECMA_FOUND ON)
	include_directories(${V8_INCLUDE_DIR})
	list (APPEND USCXML_OPT_LIBS ${V8_LIBRARY})
endif()

find_package(Lua)
if (LUA_FOUND)
	include_directories (${LUA_INCLUDE_DIR})
	include_directories(${PROJECT_SOURCE_DIR}/contrib/src/LuaBridge)
	list (APPEND USCXML_OPT_LIBS ${LUA_LIBRARIES})
endif()

add_subdirectory(src/uscxml)

add_library(uscxml ${USCXML_FILES})
set_property(TARGET uscxml PROPERTY CXX_STANDARD 11)
set_property(TARGET uscxml PROPERTY CXX_STANDARD_REQUIRED ON)
set_property(TARGET uscxml PROPERTY SOVERSION ${USCXML_VERSION})

add_dependencies(uscxml ${USCXML_PREREQS})
target_link_libraries(uscxml ${USCXML_OPT_LIBS} ${USCXML_CORE_LIBS})

add_library(uscxml_transform ${USCXML_TRANSFORM_FILES})
set_property(TARGET uscxml_transform PROPERTY CXX_STANDARD 11)
set_property(TARGET uscxml_transform PROPERTY CXX_STANDARD_REQUIRED ON)
set_property(TARGET uscxml_transform PROPERTY SOVERSION ${USCXML_VERSION})
target_link_libraries(uscxml_transform uscxml)

if (NOT CMAKE_CROSSCOMPILING)
	enable_testing()
	add_subdirectory(test)
endif()

if (WIN32)
	add_executable(uscxml-browser apps/uscxml-browser.cpp ${PROJECT_SOURCE_DIR}/contrib/src/getopt/getopt.c)
	add_executable(uscxml-transform apps/uscxml-transform.cpp ${PROJECT_SOURCE_DIR}/contrib/src/getopt/getopt.c)
else()
	add_executable(uscxml-browser apps/uscxml-browser.cpp)
	add_executable(uscxml-transform apps/uscxml-transform.cpp)
endif()

set_property(TARGET uscxml-browser PROPERTY CXX_STANDARD 11)
set_property(TARGET uscxml-browser PROPERTY CXX_STANDARD_REQUIRED ON)
set_property(TARGET uscxml-transform PROPERTY CXX_STANDARD 11)
set_property(TARGET uscxml-transform PROPERTY CXX_STANDARD_REQUIRED ON)

target_link_libraries(uscxml-browser uscxml)
target_link_libraries(uscxml-transform uscxml uscxml_transform)


############################################################
# Create config.h
############################################################

# determine path seperator
if (WIN32)
    SET(PATH_SEPERATOR "\\\\")
else()
	SET(PATH_SEPERATOR "/")
endif()

if(CMAKE_BUILD_TYPE STREQUAL "Release")
	set(CMAKE_BUILD_TYPE_RELEASE ON)
elseif(CMAKE_BUILD_TYPE STREQUAL "Debug")
	set(CMAKE_BUILD_TYPE_DEBUG ON)
endif()

# enable config.h style compile time options and add as "uscxml/config.h"
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/config.h.in ${CMAKE_CURRENT_BINARY_DIR}/uscxml/config.h)
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/test/ctest/CTestCustom.ctest.in ${CMAKE_CURRENT_BINARY_DIR}/CTestCustom.ctest)

# get_cmake_property(_variableNames VARIABLES)
# foreach (_variableName ${_variableNames})
#     message(STATUS "${_variableName}=${${_variableName}}")
# endforeach()
