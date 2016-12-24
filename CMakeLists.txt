# travis build slaves ony feature 2.8.7 - let's hope it's sufficient
cmake_minimum_required(VERSION 2.8.7 FATAL_ERROR)

# build type has to be set before the project definition
SET(BUILD_TYPE_HELP "Choose the type of build, options are: None(CMAKE_CXX_FLAGS or CMAKE_C_FLAGS used) Debug, Release, RelWithDebInfo, MinSizeRel.")
IF(DEFINED CMAKE_BUILD_TYPE)
   SET(CMAKE_BUILD_TYPE ${CMAKE_BUILD_TYPE} CACHE STRING ${BUILD_TYPE_HELP})
ELSE()
   SET(CMAKE_BUILD_TYPE Release CACHE STRING ${BUILD_TYPE_HELP})
ENDIF()

PROJECT(uSCXML)

#################################################
# General Setup
#################################################

# where to find more cmake scripts
set(CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/contrib/cmake)
include("${CMAKE_MODULE_PATH}/USCXMLMacros.cmake")

# use folders in the IDEs for the various targets
set_property(GLOBAL PROPERTY USE_FOLDERS ON)

# use rpath with MacOSX
set(CMAKE_MACOSX_RPATH 1)

# specify USCXML version
SET(USCXML_VERSION_MAJOR "2")
SET(USCXML_VERSION_MINOR "0")
SET(USCXML_VERSION_PATCH "0")
SET(USCXML_VERSION ${USCXML_VERSION_MAJOR}.${USCXML_VERSION_MINOR}.${USCXML_VERSION_PATCH})

# Normalize CMAKE_SYSTEM_PROCESSOR for build target
if(CMAKE_SIZEOF_VOID_P EQUAL 8)
	set(64BIT_HOST ON)
	set(64BIT_SUFFIX "_64")
endif()

if (${CMAKE_SYSTEM_PROCESSOR} STREQUAL "AMD64")
  set(CMAKE_SYSTEM_PROCESSOR "x86${64BIT_SUFFIX}")
endif()
if (${CMAKE_SYSTEM_PROCESSOR} STREQUAL "i386")
  set(CMAKE_SYSTEM_PROCESSOR "x86${64BIT_SUFFIX}")
endif()
if (${CMAKE_SYSTEM_PROCESSOR} STREQUAL "x86_64")
  set(CMAKE_SYSTEM_PROCESSOR "x86${64BIT_SUFFIX}")
endif()


# determine platform id
SET(USCXML_PLATFORM_ID)
string(TOLOWER ${CMAKE_SYSTEM_NAME} CMAKE_SYSTEM_NAME_LC)
string(TOLOWER ${CMAKE_CXX_COMPILER_ID} CMAKE_CXX_COMPILER_ID_LC)
string(TOLOWER ${CMAKE_SYSTEM_PROCESSOR} CMAKE_SYSTEM_PROCESSOR_LC)
set(USCXML_PLATFORM_ID "${CMAKE_SYSTEM_NAME_LC}-${CMAKE_SYSTEM_PROCESSOR_LC}-${CMAKE_CXX_COMPILER_ID_LC}")

# figure out MacOSX version and C++ library
if (APPLE)
	set(LIBCPP_NAME "libstdc++") # before mavericks
	# get MacOSX version
	execute_process(
		COMMAND /usr/bin/sw_vers -productVersion 
		OUTPUT_VARIABLE MACOSX_VERSION
		OUTPUT_STRIP_TRAILING_WHITESPACE)
	if (MACOSX_VERSION)
		THREE_PART_VERSION_TO_VARS(
			${MACOSX_VERSION}
			MACOSX_VERSION_MAJOR 
			MACOSX_VERSION_MINOR 
			MACOSX_VERSION_PATCH)
	endif()
	if (MACOSX_VERSION VERSION_GREATER "10.8.99")
		set(LIBCPP_NAME "libc++") # mavericks and above
		# set(CMAKE_FIND_ROOT_PATH ${CMAKE_OSX_SYSROOT} ${CMAKE_FIND_ROOT_PATH})
	endif()
	set(USCXML_PLATFORM_ID "${USCXML_PLATFORM_ID}-${LIBCPP_NAME}")
endif()

if (MSVC)
	set(USCXML_PLATFORM_ID "${USCXML_PLATFORM_ID}-${MSVC_VERSION}")
endif()

# where do libraries and binaries go
set (CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)
set (CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set (CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)

# setup header include paths
include_directories(src)
include_directories(contrib/src)
include_directories(${CMAKE_BINARY_DIR})
include_directories(${PROJECT_SOURCE_DIR}/contrib/src/jsmn)
include_directories(${PROJECT_SOURCE_DIR}/contrib/src/evws)

set(GETOPT_FILES ${PROJECT_SOURCE_DIR}/contrib/src/uscxml/InterpreterOptions.cpp)	
if (WIN32)
	include_directories(${PROJECT_SOURCE_DIR}/contrib/src/getopt)
	include_directories(${PROJECT_SOURCE_DIR}/contrib/src/inttypes)
	list(APPEND GETOPT_FILES ${PROJECT_SOURCE_DIR}/contrib/src/getopt/getopt.c)	
endif()

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
check_cxx_source_compiles("
	class Foo { int x = 8; }; int main(){}
" CXX_HAS_MEMBER_INIT)
check_cxx_source_compiles("
	#include <list>
	#include <string>
	int main(){ std::list<std::string> foo = {\"a\", \"b\"}; }
" CXX_HAS_INLINE_INIT)

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
if(NOT CXX_HAS_MEMBER_INIT)
	set(CXX_MISSING_FEATURES "${CXX_MISSING_FEATURES} member_init")
endif()
if(NOT CXX_HAS_INLINE_INIT)
	set(CXX_MISSING_FEATURES "${CXX_MISSING_FEATURES} inline_init")
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

OPTION(BUILD_BINDING_JAVA "Build language bindings for Java" ON)
OPTION(BUILD_BINDING_LUA "Build language bindings for Lua" ON)
OPTION(BUILD_BINDING_CSHARP "Build language bindings for CSharp" ON)
OPTION(BUILD_BINDING_PYTHON "Build language bindings for Python" ON)
OPTION(BUILD_BINDING_PHP "Build language bindings for PHP" OFF)


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
	# make a quick attempt to find xerces
	INCLUDE(FindPackageHandleStandardArgs)
	find_path(XercesC_INCLUDE_DIR NAMES "xercesc/util/PlatformUtils.hpp")
  find_library(XercesC_LIBRARY NAMES "xerces-c" "xerces-c_3")
  mark_as_advanced(XercesC_LIBRARIES)
	mark_as_advanced(XercesC_INCLUDE_DIR)
	if (XercesC_INCLUDE_DIR AND XercesC_LIBRARIES)
		set(XercesC_FOUND ON)
	else()
		message(STATUS "Could NOT find XercesC (your CMake distribution does not include the FindXercesC module)")
	endif()
endif()

if (XercesC_FOUND)
	include_directories(${XercesC_INCLUDE_DIRS})
	list (APPEND USCXML_CORE_LIBS ${XercesC_LIBRARIES})
	set(XERCESC_NS "xercesc_3_1")
else()
	message(STATUS "--> will download and compile")
	include("${CMAKE_MODULE_PATH}/BuildXercesC.cmake")
	if (XercesC_BUILT)
		include_directories(${XercesC_INCLUDE_DIRS})
		list (APPEND USCXML_CORE_LIBS ${XercesC_LIBRARIES})
		list (APPEND USCXML_PREREQS xerces-c)
		set(XERCESC_NS "xercesc_3_1")
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

#swig
if (WIN32)
	if(EXISTS "${PROJECT_BINARY_DIR}/../swig/")
		LIST(APPEND CMAKE_PROGRAM_PATH "${PROJECT_BINARY_DIR}/../swig/")
	elseif(EXISTS "${PROJECT_BINARY_DIR}/../../swig/")
		LIST(APPEND CMAKE_PROGRAM_PATH "${PROJECT_BINARY_DIR}/../../swig/")
	endif()

	file(GLOB POTENTIAL_SWIG "C:/Program Files/swig*" "C:/Program Files (x86)/swig*")
	LIST(APPEND CMAKE_PROGRAM_PATH ${POTENTIAL_SWIG}) # swig.exe
	# message(FATAL_ERROR "POTENTIAL_SWIG: ${POTENTIAL_SWIG}")
	
endif()
LIST(APPEND CMAKE_PROGRAM_PATH $ENV{SWIG_DIR})
find_package(SWIG)


# JavaScriptCore
OPTION(WITH_DM_ECMA_JSC "Do search for JavaScriptCore" ON)
if (WITH_DM_ECMA_JSC)
	find_package(JSC)
	if (JSC_FOUND)
		set(ECMA_FOUND ON)
		if (NOT APPLE)
			include_directories(${JSC_INCLUDE_DIR})
		endif()
		list (APPEND USCXML_OPT_LIBS ${JSC_LIBRARY})
	else()
		set(WITH_DM_ECMA_JSC OFF)
	endif()
endif()

# V8
OPTION(WITH_DM_ECMA_V8 "Do search for the V8 ECMAScript implementation" ON)
if (WITH_DM_ECMA_V8)
	find_package(V8)
	if (V8_FOUND)
		set(ECMA_FOUND ON)
		include_directories(${V8_INCLUDE_DIR})
		list (APPEND USCXML_OPT_LIBS ${V8_LIBRARY})
	else()
		set(WITH_DM_ECMA_V8 OFF)
	endif()
endif()

# Lua
OPTION(WITH_DM_LUA "Do search for the Lua libraries" ON)
if (WITH_DM_LUA)
	if (WIN32)
		# LuaForWindows https://code.google.com/archive/p/luaforwindows/downloads
		set(ENV{LUA_DIR} "C:/Program Files (x86)/Lua/5.1/")
	endif()
	find_package(Lua51)
	if (LUA51_FOUND)
		include_directories (${LUA_INCLUDE_DIR})
		include_directories(${PROJECT_SOURCE_DIR}/contrib/src/LuaBridge)
		list (APPEND USCXML_OPT_LIBS ${LUA_LIBRARIES})
	else()
		set(WITH_DM_LUA OFF)
	endif()
endif()

# Python
OPTION(WITH_DM_PYTHON "Do search for the Python libraries" ON)
if (WITH_DM_PYTHON)
	find_package(PythonLibs)
	if (PYTHONLIBS_FOUND)
		include_directories (${PYTHON_INCLUDE_DIRS})
		list (APPEND USCXML_OPT_LIBS ${PYTHON_LIBRARIES})
	else()
		set(WITH_DM_PYTHON ON)
	endif()
endif()

OPTION(WITH_DM_C89 "Do build with C89 datamodel support" OFF)
if (WITH_DM_C89)
	include("${CMAKE_MODULE_PATH}/BuildPicoC.cmake")
	message(STATUS "Did not look for picoc interpreter")
	message(STATUS "--> will download and compile")
	if (PICOC_BUILT)
		include_directories(${PICOC_INCLUDE_DIR})
		list (APPEND USCXML_CORE_LIBS ${PICOC_LIBRARY})
		list (APPEND USCXML_PREREQS picoc)
	else()
		message(FATAL_ERROR "Could not build picoc")
	endif()
endif()

OPTION(WITH_DM_PROMELA "Do build with promela datamodel support" ON)

add_subdirectory(src/uscxml)
add_subdirectory(src/bindings)

add_library(uscxml ${USCXML_FILES})
set_property(TARGET uscxml PROPERTY CXX_STANDARD 11)
set_property(TARGET uscxml PROPERTY CXX_STANDARD_REQUIRED ON)
set_property(TARGET uscxml PROPERTY SOVERSION ${USCXML_VERSION})
install_library(TARGETS uscxml)

add_dependencies(uscxml ${USCXML_PREREQS})
target_link_libraries(uscxml ${USCXML_OPT_LIBS} ${USCXML_CORE_LIBS})

add_library(uscxml_transform ${USCXML_TRANSFORM_FILES})
set_property(TARGET uscxml_transform PROPERTY CXX_STANDARD 11)
set_property(TARGET uscxml_transform PROPERTY CXX_STANDARD_REQUIRED ON)
set_property(TARGET uscxml_transform PROPERTY SOVERSION ${USCXML_VERSION})
target_link_libraries(uscxml_transform uscxml)
install_library(TARGETS uscxml_transform)

if (NOT CMAKE_CROSSCOMPILING)
	enable_testing()
	add_subdirectory(test)
endif()

add_executable(uscxml-browser apps/uscxml-browser.cpp ${GETOPT_FILES})
set_property(TARGET uscxml-browser PROPERTY CXX_STANDARD 11)
set_property(TARGET uscxml-browser PROPERTY CXX_STANDARD_REQUIRED ON)
install_executable(TARGETS uscxml-browser COMPONENT tools)
target_link_libraries(uscxml-browser uscxml)

add_executable(uscxml-transform apps/uscxml-transform.cpp ${GETOPT_FILES})
set_property(TARGET uscxml-transform PROPERTY CXX_STANDARD 11)
set_property(TARGET uscxml-transform PROPERTY CXX_STANDARD_REQUIRED ON)
install_executable(TARGETS uscxml-transform COMPONENT tools)
target_link_libraries(uscxml-transform uscxml uscxml_transform)

############################################################
# Documentation
############################################################

add_subdirectory(docs)

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

############################################################
# Sort files into goups in IDEs
############################################################


set(ALL_SOURCE_FILES ${USCXML_FILES} ${USCXML_TRANSFORM_FILES})
list(SORT USCXML_FILES)
list(SORT USCXML_TRANSFORM_FILES)
# we cannot define source groups in sub directories!
foreach( FILE ${ALL_SOURCE_FILES} )

	get_filename_component(PATH ${FILE} PATH)
	file(RELATIVE_PATH REL_PATH ${PROJECT_SOURCE_DIR} "${PATH}")
	string(REGEX REPLACE "src/uscxml" "" REL_PATH "${REL_PATH}")
	string(REGEX REPLACE "contrib/src" "contrib" REL_PATH "${REL_PATH}")
	
	string(REGEX REPLACE "^/" "" REL_PATH "${REL_PATH}") # leading slash
	string(REGEX REPLACE "/" "\\\\" SRC_GROUP "${REL_PATH}") # escape /
	
	source_group("${SRC_GROUP}" FILES ${FILE})

endforeach()


# all variables that cmake knows about
# get_cmake_property(_variableNames VARIABLES)
# foreach (_variableName ${_variableNames})
#     message(STATUS "${_variableName}=${${_variableName}}")
# endforeach()

############################################################
# Some concluding remarks
############################################################
message(STATUS "")

set(USCXML_LIBS ${USCXML_OPT_LIBS} ${USCXML_CORE_LIBS})
list(SORT USCXML_LIBS)
message(STATUS "Linking against libraries (check if you need to export in LD_LIBRARY_PATH or PATH):")
set(SKIP_NEXT OFF)
foreach(LIBRARY ${USCXML_LIBS})
	if (LIBRARY MATCHES "debug")
		if(CMAKE_BUILD_TYPE STREQUAL "Release")
			set(SKIP_NEXT ON)
		endif()
	elseif (LIBRARY MATCHES "optimized")
		if(CMAKE_BUILD_TYPE STREQUAL "Debug")
			set(SKIP_NEXT ON)
		endif()
	else()
		if (NOT SKIP_NEXT)
			STRING(REGEX REPLACE "${CMAKE_BINARY_DIR}" "BUILD_DIR" LIBRARY ${LIBRARY})
			STRING(REGEX REPLACE "${CMAKE_SOURCE_DIR}" "SOURCE_DIR" LIBRARY ${LIBRARY})
			message(STATUS "  ${LIBRARY}")
		else()
			set(SKIP_NEXT OFF)
		endif()
	endif()
endforeach()

message(STATUS "Targets:")
message(STATUS "  Available datamodels ........... : ${USCXML_DATAMODELS}")
message(STATUS "  Available invokers ............. : ${USCXML_INVOKERS}")
message(STATUS "  Available ioprocessors ......... : ${USCXML_IOPROCESSORS}")
message(STATUS "  Available custom elements ...... : ${USCXML_ELEMENTS}")
message(STATUS "  Available language bindings .... : ${USCXML_LANGUAGE_BINDINGS}")
if (BUILD_SHARED_LIBS AND BUILD_BINDINGS)
	message(STATUS "")
	message(STATUS "    Warning: Building language bindings BUILD_SHARED_LIBS=ON")
	message(STATUS "             introduces runtime dependency to libuscxml")
	message(STATUS "")
endif()

message(STATUS "General information:")
message(STATUS "  Build type ..................... : ${CMAKE_BUILD_TYPE} for ${USCXML_PLATFORM_ID}")
if (BUILD_SHARED_LIBS)
	if (BUILD_AS_PLUGINS)
		message(STATUS "  Building library as ............ : SHARED with plugins")
	else()
		message(STATUS "  Building library as ............ : SHARED without plugins")
	endif()
else()
	if (BUILD_AS_PLUGINS)
		message(STATUS "  Building library as ............ : STATIC with plugins")
	else()
		message(STATUS "  Building library as ............ : STATIC without plugins")
	endif()
endif()

if (CMAKE_BUILD_TYPE)
string(TOUPPER ${CMAKE_BUILD_TYPE} CMAKE_BUILD_TYPE_UC)
endif()
message(STATUS "  CXX Flags   : " ${CMAKE_CXX_FLAGS} " " ${CMAKE_CXX_FLAGS_${CMAKE_BUILD_TYPE_UC}})
message(STATUS "  C   Flags   : " ${CMAKE_C_FLAGS} " " ${CMAKE_C_FLAGS_${CMAKE_BUILD_TYPE_UC}})

get_directory_property( CDEFLIST DIRECTORY ${CMAKE_SOURCE_DIR} COMPILE_DEFINITIONS )
foreach( DEF ${CDEFLIST} )
    set( CDEFS "${CDEFS} ${DEF}" )
endforeach()
message(STATUS "  Definitions : " ${CDEFS})

STRING(REGEX REPLACE "${CMAKE_BINARY_DIR}" "BUILD_DIR" REL_CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_LIBRARY_OUTPUT_DIRECTORY})
STRING(REGEX REPLACE "${CMAKE_SOURCE_DIR}" "SOURCE_DIR" REL_CMAKE_LIBRARY_OUTPUT_DIRECTORY ${REL_CMAKE_LIBRARY_OUTPUT_DIRECTORY})

STRING(REGEX REPLACE "${CMAKE_BINARY_DIR}" "BUILD_DIR" REL_CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_RUNTIME_OUTPUT_DIRECTORY})
STRING(REGEX REPLACE "${CMAKE_SOURCE_DIR}" "SOURCE_DIR" REL_CMAKE_RUNTIME_OUTPUT_DIRECTORY ${REL_CMAKE_RUNTIME_OUTPUT_DIRECTORY})

message(STATUS "  Libraries will end up in ....... : " ${REL_CMAKE_LIBRARY_OUTPUT_DIRECTORY})
message(STATUS "  Binaries will end up in ........ : " ${REL_CMAKE_RUNTIME_OUTPUT_DIRECTORY})


############################################################
# Installation / Provide package target
############################################################

# see contrib/cmake/CPackUSCXML.cmake
include(contrib/cmake/CPackUSCXML.cmake)

# cmake_policy(POP)

# This must always be last!
include(CPack)
