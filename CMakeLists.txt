cmake_minimum_required(VERSION 2.8.4)

# specify USCXML version
SET(USCXML_VERSION_MAJOR "0")
SET(USCXML_VERSION_MINOR "0")
SET(USCXML_VERSION_PATCH "4")
SET(USCXML_VERSION ${USCXML_VERSION_MAJOR}.${USCXML_VERSION_MINOR}.${USCXML_VERSION_PATCH})

# build type has to be set before the project definition
SET(BUILD_TYPE_HELP "Choose the type of build, options are: None(CMAKE_CXX_FLAGS or CMAKE_C_FLAGS used) Debug, Release, RelWithDebInfo, MinSizeRel.")
IF(DEFINED CMAKE_BUILD_TYPE)
   SET(CMAKE_BUILD_TYPE ${CMAKE_BUILD_TYPE} CACHE STRING ${BUILD_TYPE_HELP})
ELSE()
   SET(CMAKE_BUILD_TYPE Debug CACHE STRING ${BUILD_TYPE_HELP})
ENDIF()

project(uscxml)
# use folders in the IDEs for the various targets (e.g. Library, Testing, Tools ..)
set_property(GLOBAL PROPERTY USE_FOLDERS ON)

# lower case version of system name and compiler for library paths
string(TOLOWER ${CMAKE_SYSTEM_NAME} CMAKE_SYSTEM_NAME_LC)
string(TOLOWER ${CMAKE_CXX_COMPILER_ID} CMAKE_CXX_COMPILER_ID_LC)

############################################################
# Search paths for cross compiling and prebuilds
############################################################

# this happens when we ssh into windows to build there, see also:
# http://publib.boulder.ibm.com/infocenter/wxdinfo/v6r1/index.jsp?topic=/com.ibm.websphere.ops.doc/info/odoe_task/tcimgr_sshwin.html
if (NOT CMAKE_SYSTEM_PROCESSOR)
	set(CMAKE_SYSTEM_PROCESSOR x86)
endif()

# is this a 64Bit host?
if(CMAKE_SIZEOF_VOID_P EQUAL 8)
	set(64BIT_HOST ON)
	set(64BIT_LIB_POSTFIX 64)
	# additional library paths to be searched
	set(FIND_LIBRARY_USE_LIB64_PATHS ON)
# 	LIST(APPEND CMAKE_FIND_ROOT_PATH "/usr/local/lib64")
# 	LIST(APPEND CMAKE_FIND_ROOT_PATH "/usr/lib64")
endif()

# We use the toolchain file from http://code.google.com/p/android-cmake/
if (CMAKE_CROSSCOMPILING AND ANDROID_ABI)
	set(ANDROID ON)
	set(CMAKE_CROSSCOMPILING_TARGET android)
	set(CMAKE_SYSTEM_VERSION ${ANDROID_NATIVE_API_LEVEL})
endif()

#
# Setting the CMAKE_FIND_ROOT_PATH to a list of directories will cause all CMake modules
# to look in these directories in addition to the system search paths:
# http://www.vtk.org/Wiki/CMake_Cross_Compiling#Searching_and_finding_external_software
#

SET(USCXML_PREBUILT_LIBRARY_PATH)
SET(USCXML_PREBUILT_HEADER_PATH "${PROJECT_SOURCE_DIR}/contrib/prebuilt")
# search roots for libraries
if(CMAKE_CROSSCOMPILING)
	SET(CMAKE_FIND_ROOT_PATH_MODE_INCLUDE "ONLY")
	if (IOS)
		SET(CMAKE_FIND_ROOT_PATH_MODE_LIBRARY "ONLY")
		SET(USCXML_PREBUILT_LIBRARY_PATH "${PROJECT_SOURCE_DIR}/contrib/prebuilt/ios/${CMAKE_SYSTEM_VERSION}")
	elseif (ANDROID)
		SET(CMAKE_FIND_ROOT_PATH_MODE_LIBRARY "ONLY") # we need both to find jni - we don't?
		SET(CMAKE_FIND_ROOT_PATH_MODE_PROGRAM "BOTH")
		SET(CMAKE_FIND_ROOT_PATH_MODE_INCLUDE "BOTH")
		SET(USCXML_PREBUILT_LIBRARY_PATH "${PROJECT_SOURCE_DIR}/contrib/prebuilt/android/${ANDROID_ABI}")
		LIST(APPEND CMAKE_FIND_ROOT_PATH "/usr/local/bin") # this is needed to find swig
		LIST(APPEND CMAKE_FIND_ROOT_PATH "/opt/local/bin") # this is needed to find protoc
	endif ()
else ()
	# SET(CMAKE_FIND_ROOT_PATH_MODE_PROGRAM "BOTH")
	# SET(CMAKE_FIND_ROOT_PATH_MODE_INCLUDE "BOTH")
	# SET(CMAKE_FIND_ROOT_PATH_MODE_LIBRARY "BOTH")
	if (WIN32 AND 64BIT_HOST)
		SET(USCXML_PREBUILT_LIBRARY_PATH "${PROJECT_SOURCE_DIR}/contrib/prebuilt/${CMAKE_SYSTEM_NAME_LC}-${CMAKE_SYSTEM_PROCESSOR}_64/${CMAKE_CXX_COMPILER_ID_LC}")
	else()
		SET(USCXML_PREBUILT_LIBRARY_PATH "${PROJECT_SOURCE_DIR}/contrib/prebuilt/${CMAKE_SYSTEM_NAME_LC}-${CMAKE_SYSTEM_PROCESSOR}/${CMAKE_CXX_COMPILER_ID_LC}")
	endif()
endif()

SET(USCXML_LIBRARY_HOST_URL_PREFIX "http://uscxml.tk.informatik.tu-darmstadt.de/prebuilt" CACHE STRING "The root path of an URL where to look for prebuilt libraries.")

if (WIN32 AND 64BIT_HOST)
	SET(USCXML_LIBRARY_ARCHIVE_NAME uscxml-prebuilt-${CMAKE_SYSTEM_NAME_LC}-${CMAKE_SYSTEM_PROCESSOR}_64.tgz)
else()
	SET(USCXML_LIBRARY_ARCHIVE_NAME uscxml-prebuilt-${CMAKE_SYSTEM_NAME_LC}-${CMAKE_SYSTEM_PROCESSOR}.tgz)
endif()

if (NOT EXISTS ${USCXML_PREBUILT_LIBRARY_PATH})
	message(STATUS "Downloading prebuilt libraries: ${USCXML_LIBRARY_HOST_URL_PREFIX}/${USCXML_VERSION}/${USCXML_LIBRARY_ARCHIVE_NAME}")
	file(DOWNLOAD ${USCXML_LIBRARY_HOST_URL_PREFIX}/${USCXML_VERSION}/${USCXML_LIBRARY_ARCHIVE_NAME}
		${PROJECT_SOURCE_DIR}/contrib/prebuilt/${USCXML_LIBRARY_ARCHIVE_NAME}
		INACTIVITY_TIMEOUT 60 STATUS DOWNLOAD_STATUS  SHOW_PROGRESS)
	list(GET DOWNLOAD_STATUS 0 STATUS_CODE)
	list(GET DOWNLOAD_STATUS 1 STATUS_STRING)
	if(STATUS_CODE EQUAL 0)
		execute_process(
			COMMAND ${CMAKE_COMMAND} -E tar xzf ${PROJECT_SOURCE_DIR}/contrib/prebuilt/${USCXML_LIBRARY_ARCHIVE_NAME}
			WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}/contrib/prebuilt/
		)
		execute_process(
			COMMAND ${CMAKE_COMMAND} -E remove ${PROJECT_SOURCE_DIR}/contrib/prebuilt/${USCXML_LIBRARY_ARCHIVE_NAME}
			WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}/contrib/prebuilt/
		)
	else()
		message("Downloading prebuilt libraries failed with ${STATUS_STRING} - maybe this platform is not supported?")
	endif()
endif()

#
# BUILD_PREFER_PREBUILT_LIBS:
# Do we want to search system paths or contrib/prebuilt first?
#
if (CMAKE_CROSSCOMPILING)
	# always prefer prebuilt libraries for cross-compiling
	OPTION(BUILD_PREFER_PREBUILT_LIBS "Search libraries in contrib/prebuilt first" ON)
	SET(CMAKE_FIND_ROOT_PATH "${USCXML_PREBUILT_LIBRARY_PATH};${USCXML_PREBUILT_HEADER_PATH};${CMAKE_FIND_ROOT_PATH}")
else()
	OPTION(BUILD_PREFER_PREBUILT_LIBS "Search libraries in contrib/prebuilt first" ON)
	if (BUILD_PREFER_PREBUILT_LIBS)
		# for everything, we start our search in contrib/prebuilt
		SET(CMAKE_FIND_ROOT_PATH "${USCXML_PREBUILT_LIBRARY_PATH};${USCXML_PREBUILT_HEADER_PATH};${CMAKE_FIND_ROOT_PATH}")
	else()
		# using this trick, we search paths from find_* before CMAKE_FIND_ROOT_PATH as '/' is prepended first
		SET(CMAKE_FIND_ROOT_PATH "/;${CMAKE_FIND_ROOT_PATH};${USCXML_PREBUILT_LIBRARY_PATH};${USCXML_PREBUILT_HEADER_PATH}")
	endif()
endif()
include_directories(${USCXML_PREBUILT_LIBRARY_PATH}/include)

#message("CMAKE_FIND_ROOT_PATH: ${CMAKE_FIND_ROOT_PATH}")

if (WIN32)
	include_directories(${PROJECT_SOURCE_DIR}/contrib/src/getopt)
endif()
include_directories(${PROJECT_SOURCE_DIR}/contrib/src/jsmn)

############################################################
# General setup
############################################################

# enable testing and actual output with tests
if (CMAKE_CROSSCOMPILING)
	OPTION(BUILD_TESTS "Build USCXML tests" OFF)
else()
	OPTION(BUILD_TESTS "Build USCXML tests" ON)
	OPTION(RUN_W3C_TESTS "Run W3C tests" ON)
endif()

# a dummy target to depend on the targets needed for tests, see:
# http://stackoverflow.com/questions/733475/cmake-ctest-make-test-doesnt-build-tests
add_custom_target(ALL_TESTS COMMENT "Building all tests when BUILD_TESTS is enabled")
if (BUILD_TESTS)
	enable_testing()
	SET(ENV{CTEST_OUTPUT_ON_FAILURE} ON)
endif()

OPTION(DIST_PREPARE "Put libraries into the lib folder of the source tree" OFF)

# where to find the cmake modules we distribute
set(CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/contrib/cmake)
include("${CMAKE_MODULE_PATH}/USCXMLMacros.cmake")
include("${CMAKE_MODULE_PATH}/FunctionExists.cmake")
include("${CMAKE_MODULE_PATH}/HeaderExists.cmake")

# we need USCXML_CORE_LIBS here for -lgcov
set(USCXML_CORE_LIBS)
set(USCXML_OPT_LIBS)
set(USCXML_FILES)

# some compiler flags
#message("CMAKE_CXX_COMPILER_ID: ${CMAKE_CXX_COMPILER_ID}")

if(${CMAKE_CXX_COMPILER_ID} STREQUAL "GNU")
	execute_process(COMMAND ${CMAKE_C_COMPILER} -dumpversion OUTPUT_VARIABLE GCC_VERSION)

	# best practices from scott meyers
	#	add_definitions(-Weffc++)

  # order of arguments of gcc matters again
#	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fPIC")
	add_definitions(-fPIC)
	add_definitions(-Wunreachable-code)

	if (CMAKE_BUILD_TYPE MATCHES ".*Deb.*") # when not building for debug
		# coverage information
		add_definitions(-fprofile-arcs)
		add_definitions(-ftest-coverage)
		list (APPEND USCXML_CORE_LIBS "gcov")
	endif()

	# all warnings
	add_definitions(-Wall)
#	add_definitions(-Wno-parentheses-equality)
	add_definitions(-Wno-attributes)

	# we cannot tread warning as error with the "narrowing problem"
	# add_definitions(-Werror)

	if(GCC_VERSION VERSION_EQUAL 4.7 OR GCC_VERSION VERSION_GREATER 4.7)
		# when compiling as C++11, narrowing is a warning but older compilers complain about the option
		add_definitions(-Wno-narrowing)
	endif()

	# swig will throw a warning with optimization otherwise
	add_definitions(-fno-strict-aliasing)
	add_definitions("-Wno-unused-value -Wno-sign-compare")
#	add_definitions(-Wno-unused-function)
	if (NOT CMAKE_BUILD_TYPE MATCHES ".*Deb.*") # when not building for debug
		# add_definitions("-s")
    	#set(CMAKE_CXX_FLAGS "-s")  ## Strip binary for everything but debug builds
    	# set(CMAKE_EXE_LINKER_FLAGS "-Wl,--gc-sections")
		# add_definitions("-mpreferred-stack-boundary=4")
		# add_definitions("-fmerge-constants")
		# add_definitions("-fno-rtti -DBOOST_NO_TYPEID")
		# add_definitions("-fno-exceptions")
		# add_definitions("-fno-inline")
		# add_definitions("-ffunction-sections -fdata-sections")
	else()
		add_definitions(-rdynamic)
	endif()
elseif (${CMAKE_CXX_COMPILER_ID} STREQUAL "MSVC")
	add_definitions("-DZMQ_STATIC")
	add_definitions("-DPCRE_STATIC")
	add_definitions("-DUMUNDO_STATIC")
	add_definitions("-D_SCL_SECURE_NO_WARNINGS")
	add_definitions("-D_CRT_SECURE_NO_WARNINGS")
	add_definitions("/bigobj")
	
	# SET(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} /NODEFAULTLIB")
	# SET(CMAKE_EXE_LINKER_FLAGS_DEBUG "${CMAKE_EXE_LINKER_FLAGS_DEBUG} /NODEFAULTLIB:MSVCRTD.lib")
elseif (${CMAKE_CXX_COMPILER_ID} STREQUAL "Clang")
	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wno-parentheses-equality")
	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wno-string-plus-int")
	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wno-non-literal-null-conversion")
	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wno-null-conversion")
	
	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fPIC")
	# set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -read_only_relocs suppress")
	# set(CMAKE_EXE_LINKER_FLAGS_DEBUG "${CMAKE_EXE_LINKER_FLAGS_DEBUG} -read_only_relocs suppress")
else()
	message(FATAL_ERROR "Unknown compiler: ${CMAKE_CXX_COMPILER_ID}")
endif()

set(CMAKE_COMPILER_STRING "${CMAKE_CXX_COMPILER_ID} ${CMAKE_CXX_COMPILER_VERSION}")

############################################################
# postfixes for all built targets depending on build type
############################################################

SET(CMAKE_DEBUG_POSTFIX "${64BIT_LIB_POSTFIX}_d")
SET(CMAKE_RELEASE_POSTFIX "${64BIT_LIB_POSTFIX}")
SET(CMAKE_RELWITHDEBINFO_POSTFIX "${64BIT_LIB_POSTFIX}_rd")
SET(CMAKE_MINSIZEREL_POSTFIX "${64BIT_LIB_POSTFIX}_s")

SET(CMAKE_LIBRARY_POSTFIX ${CMAKE_${BUILD_TYPE}_POSTFIX})

if (UNIX)
	add_definitions(-DHAVE_SYS_SOCKET_H)
endif()

############################################################
# Library location, type and linking
############################################################

# built shared or static libraries?
if(BUILD_SHARED_LIBS)
	add_definitions("-DCOMPILING_DLL")
else()
	add_definitions("-DUSCXML_STATIC")
endif()

# prefer static libraries for linking
if(BUILD_PREFER_STATIC_LIBRARIES)
    SET(CMAKE_FIND_LIBRARY_SUFFIXES .lib .a ${CMAKE_FIND_LIBRARY_SUFFIXES})
endif()

# where should libraries end up?
if (DIST_PREPARE)
	if (CMAKE_CROSSCOMPILING)
		string(TOLOWER ${CMAKE_CROSSCOMPILING_TARGET} CMAKE_CROSSCOMPILING_TARGET_LC)
		set(OUTPUT_DIR
			${PROJECT_SOURCE_DIR}/package/cross-compiled/${CMAKE_CROSSCOMPILING_TARGET_LC}-${CMAKE_SYSTEM_VERSION}/${CMAKE_SYSTEM_PROCESSOR})
	else()
		if (WIN32 AND 64BIT_HOST)
			set(OUTPUT_DIR
				${PROJECT_SOURCE_DIR}/package/${CMAKE_SYSTEM_NAME_LC}-${CMAKE_SYSTEM_PROCESSOR}_64/${CMAKE_CXX_COMPILER_ID_LC})
		else()
			set(OUTPUT_DIR
				${PROJECT_SOURCE_DIR}/package/${CMAKE_SYSTEM_NAME_LC}-${CMAKE_SYSTEM_PROCESSOR}/${CMAKE_CXX_COMPILER_ID_LC})
		endif()
	endif()
else()
	set(OUTPUT_DIR ${PROJECT_BINARY_DIR})
endif()

set( CMAKE_RUNTIME_OUTPUT_DIRECTORY "${OUTPUT_DIR}/bin" )
set( CMAKE_LIBRARY_OUTPUT_DIRECTORY "${OUTPUT_DIR}/lib" )
set( CMAKE_ARCHIVE_OUTPUT_DIRECTORY "${OUTPUT_DIR}/lib" )
foreach( OUTPUT_CONFIG ${CMAKE_CONFIGURATION_TYPES} )
    string( TOUPPER ${OUTPUT_CONFIG} OUTPUT_CONFIG )
    set( CMAKE_RUNTIME_OUTPUT_DIRECTORY_${OUTPUT_CONFIG} "${OUTPUT_DIR}/bin" )
    set( CMAKE_LIBRARY_OUTPUT_DIRECTORY_${OUTPUT_CONFIG} "${OUTPUT_DIR}/lib" )
    set( CMAKE_ARCHIVE_OUTPUT_DIRECTORY_${OUTPUT_CONFIG} "${OUTPUT_DIR}/lib" )
endforeach()

# this is where the config.h ends up
include_directories(${CMAKE_CURRENT_BINARY_DIR})

############################################################
# Dependent libraries
############################################################

if (NOT WIN32)
	# libxml2
	find_package(LibXml2 REQUIRED)
	include_directories(${LIBXML2_INCLUDE_DIR})
	list (APPEND USCXML_CORE_LIBS ${LIBXML2_LIBRARIES})
	set(XML_LIBRARIES ${LIBXML2_LIBRARIES})
elseif(WIN32)
	list (APPEND XML_LIBRARIES "Ws2_32")
	list (APPEND XML_LIBRARIES "Winmm")
	list (APPEND XML_LIBRARIES "Iphlpapi")
	list (APPEND XML_LIBRARIES "Netapi32")
	list (APPEND USCXML_CORE_LIBS ${XML_LIBRARIES})
endif()


# CURL
find_package(CURL REQUIRED)
# find_package(OpenSSL REQUIRED)
# find_package(ZLIB REQUIRED)

# include_directories(${OPENSSL_INCLUDE_DIR})
# include_directories(${ZLIB_INCLUDE_DIRS})
include_directories(${CURL_INCLUDE_DIRS})
list (APPEND USCXML_CORE_LIBS ${CURL_LIBRARIES})
# list (APPEND USCXML_CORE_LIBS ${OPENSSL_LIBRARIES})
# list (APPEND USCXML_CORE_LIBS ${ZLIB_LIBRARIES})
if (WIN32)
	add_definitions("-DCURL_STATICLIB")
endif()


# prefer rest as static libraries
set(CMAKE_FIND_LIBRARY_SUFFIXES_ORIG ${CMAKE_FIND_LIBRARY_SUFFIXES})
set(CMAKE_FIND_LIBRARY_SUFFIXES .lib .a ${CMAKE_FIND_LIBRARY_SUFFIXES})

################################
# required libraries for core


# GLOG

# set(ENV{GLOG_SRC} ${CMAKE_SOURCE_DIR}/../glog)
find_package(GLOG REQUIRED)
include_directories(${GLOG_INCLUDE_DIR})
list (APPEND USCXML_CORE_LIBS ${GLOG_LIBRARY})
add_definitions(-DGLOG_NO_ABBREVIATED_SEVERITIES)


# ARABICA

# set($ENV{ARABICA_SRC} ${PROJECT_SOURCE_DIR}/../arabica)
find_package(Arabica REQUIRED)
include_directories(${ARABICA_INCLUDE_DIR})
list (APPEND USCXML_CORE_LIBS ${ARABICA_LIBRARY})
if (WIN32)
	add_definitions("-DUSE_MSXML")
endif()


# BOOST - header only

FIND_PATH(Boost_INCLUDE_DIR boost/version.hpp)
include_directories(${Boost_INCLUDE_DIR})


# LIBEVENT

#set(ENV{EVENT_SRC} ${CMAKE_SOURCE_DIR}/../libevent)
find_package(EVENT REQUIRED)
include_directories(${EVENT_INCLUDE_DIR})
list (APPEND USCXML_CORE_LIBS ${EVENT_LIBRARY})

############################################################
# Actual files of core library
############################################################

file(GLOB_RECURSE USCXML_SERVER
	src/uscxml/server/*.cpp
	src/uscxml/server/*.h
)
source_group("Interpreter" FILES ${USCXML_SERVER})
list (APPEND USCXML_FILES ${USCXML_SERVER})

file(GLOB_RECURSE USCXML_CONCURRENCY
	src/uscxml/concurrency/*.cpp
	src/uscxml/concurrency/*.h
)
source_group("Interpreter" FILES ${USCXML_CONCURRENCY})
list (APPEND USCXML_FILES ${USCXML_CONCURRENCY})

file(GLOB_RECURSE USCXML_DEBUG
	src/uscxml/debug/*.cpp
	src/uscxml/debug/*.h
)
source_group("Interpreter" FILES ${USCXML_DEBUG})
list (APPEND USCXML_FILES ${USCXML_DEBUG})

file(GLOB_RECURSE USCXML_INTERPRETERS
	src/uscxml/interpreter/*.cpp
	src/uscxml/interpreter/*.h
)
source_group("Interpreter" FILES ${USCXML_INTERPRETERS})
list (APPEND USCXML_FILES ${USCXML_INTERPRETERS})

file(GLOB USCXML_CORE
	contrib/src/jsmn/jsmn.c
	src/uscxml/*.cpp
	src/uscxml/*.h
)
source_group("Interpreter" FILES ${USCXML_CORE})
list (APPEND USCXML_FILES ${USCXML_CORE})

include_directories(src)

OPTION(BUILD_AS_PLUGINS "Build invokers, ioprocessors and datamodels as plugins" OFF)
if (BUILD_AS_PLUGINS)
	include_directories(${PROJECT_SOURCE_DIR}/src/uscxml/plugins)
	file(GLOB PLUMA 
		src/uscxml/plugins/Pluma/*.cpp 
		src/uscxml/plugins/Pluma/*.h
		src/uscxml/plugins/*.cpp 
		src/uscxml/plugins/*.h
	)
	source_group("Interpreter" FILES ${PLUMA})
	list (APPEND USCXML_FILES ${PLUMA})
	add_definitions("-DBUILD_AS_PLUGINS")
endif()

if (BUILD_AS_PLUGINS)
	add_library(uscxml ${USCXML_FILES})
endif()

#################################################
# optional things we can build as plugins

# sample invoker - include to make sure it compiles
file(GLOB_RECURSE SAMPLE_INVOKER
	src/uscxml/plugins/invoker/sample/*.cpp
	src/uscxml/plugins/invoker/sample/*.h
)
source_group("Invoker\\sample" FILES ${SAMPLE_INVOKER})
if (BUILD_AS_PLUGINS)
	add_library(
		invoker_sample SHARED 
		${SAMPLE_INVOKER})
	target_link_libraries(invoker_sample uscxml)
	set_target_properties(invoker_sample PROPERTIES FOLDER "Plugin Invoker")
else()
	list (APPEND USCXML_FILES ${SAMPLE_INVOKER})
endif()


# LIBEVENT basichttp ioprocessor - this one is already required above

file(GLOB_RECURSE BASICHTTP_IOPROCESSOR
	src/uscxml/plugins/ioprocessor/basichttp/*.cpp
	src/uscxml/plugins/ioprocessor/basichttp/*.h
)
source_group("IOProcessor\\basichttp" FILES ${BASICHTTP_IOPROCESSOR})
if (BUILD_AS_PLUGINS)
	add_library(
		ioprocessor_basichttp SHARED 
		${BASICHTTP_IOPROCESSOR})
	target_link_libraries(ioprocessor_basichttp uscxml)
	set_target_properties(ioprocessor_basichttp PROPERTIES FOLDER "Plugin IOProcessor")
else()
	list (APPEND USCXML_FILES ${BASICHTTP_IOPROCESSOR})
endif()


# scxml ioprocessor - this one is already required above

file(GLOB_RECURSE SCXML_IOPROCESSOR
	src/uscxml/plugins/ioprocessor/scxml/*.cpp
	src/uscxml/plugins/ioprocessor/scxml/*.h
)
source_group("IOProcessor\\scxml" FILES ${SCXML_IOPROCESSOR})
if (BUILD_AS_PLUGINS)
	add_library(
		ioprocessor_scxml SHARED 
		${SCXML_IOPROCESSOR})
	target_link_libraries(ioprocessor_scxml uscxml)
	set_target_properties(ioprocessor_scxml PROPERTIES FOLDER "Plugin IOProcessor")
else()
	list (APPEND USCXML_FILES ${SCXML_IOPROCESSOR})
endif()


# Fetch element

file(GLOB_RECURSE FETCH_ELEMENT
	src/uscxml/plugins/element/fetch/*.cpp
	src/uscxml/plugins/element/fetch/*.h
)
source_group("Element\\fetch" FILES ${FETCH_ELEMENT})
if (BUILD_AS_PLUGINS)
	add_library(
		element_fetch SHARED 
		${FETCH_ELEMENT})
	target_link_libraries(element_fetch uscxml)
	set_target_properties(element_fetch PROPERTIES FOLDER "Plugin Element")
else()
	list (APPEND USCXML_FILES ${FETCH_ELEMENT})
endif()


# Postpone element

file(GLOB_RECURSE POSTPONE_ELEMENT
	src/uscxml/plugins/element/postpone/*.cpp
	src/uscxml/plugins/element/postpone/*.h
)
source_group("Element\\postpone" FILES ${POSTPONE_ELEMENT})
if (BUILD_AS_PLUGINS)
	add_library(
		element_postpone SHARED 
		${POSTPONE_ELEMENT})
	target_link_libraries(element_postpone uscxml)
	set_target_properties(element_postpone PROPERTIES FOLDER "Plugin Element")
else()
	list (APPEND USCXML_FILES ${POSTPONE_ELEMENT})
endif()


# Response element

file(GLOB_RECURSE RESPONSE_ELEMENT
	src/uscxml/plugins/element/response/*.cpp
	src/uscxml/plugins/element/response/*.h
)
source_group("Element\\response" FILES ${RESPONSE_ELEMENT})
if (BUILD_AS_PLUGINS)
	add_library(
		element_response SHARED 
		${RESPONSE_ELEMENT})
	target_link_libraries(element_response uscxml)
	set_target_properties(element_response PROPERTIES FOLDER "Plugin Element")
else()
	list (APPEND USCXML_FILES ${RESPONSE_ELEMENT})
endif()


# DirMon invoker to watch for filesystem changes

file(GLOB_RECURSE DIRMON_INVOKER
	src/uscxml/plugins/invoker/filesystem/dirmon/*.cpp
	src/uscxml/plugins/invoker/filesystem/dirmon/*.h
)
source_group("Invoker\\dirmon" FILES ${DIRMON_INVOKER})
include_directories(${PROJECT_SOURCE_DIR}/src/uscxml/plugins/invoker/filesystem/dirmon/)
if (BUILD_AS_PLUGINS)
	add_library(
		invoker_dirmon SHARED 
		${DIRMON_INVOKER})
	target_link_libraries(invoker_dirmon uscxml)
	set_target_properties(invoker_dirmon PROPERTIES FOLDER "Plugin Invoker")
else()
	list (APPEND USCXML_FILES ${DIRMON_INVOKER})
endif()


# System invoker to open a native command

file(GLOB_RECURSE SYSTEM_INVOKER
	src/uscxml/plugins/invoker/system/*.cpp
	src/uscxml/plugins/invoker/system/*.h
)
source_group("Invoker\\system" FILES ${SYSTEM_INVOKER})
include_directories(${PROJECT_SOURCE_DIR}/src/uscxml/plugins/invoker/system/)
if (BUILD_AS_PLUGINS)
	add_library(
		invoker_system SHARED 
		${SYSTEM_INVOKER})
	target_link_libraries(invoker_system uscxml)
	set_target_properties(invoker_system PROPERTIES FOLDER "Plugin Invoker")
else()
	list (APPEND USCXML_FILES ${SYSTEM_INVOKER})
endif()


# SQLite3 SQL Invoker

find_package(Sqlite3)
if (SQLITE3_FOUND)
	file(GLOB_RECURSE SQLITE3_INVOKER
		src/uscxml/plugins/invoker/sqlite3/*.cpp
		src/uscxml/plugins/invoker/sqlite3/*.h
	)
	source_group("Invoker\\sqlite" FILES ${SQLITE3_INVOKER})
	if (BUILD_AS_PLUGINS)
		add_library(
			invoker_sqlite3 SHARED 
			${SQLITE3_INVOKER})
		target_link_libraries(invoker_sqlite3 uscxml)
		set_target_properties(invoker_sqlite3 PROPERTIES FOLDER "Plugin Invoker")
	else()
		list (APPEND USCXML_FILES ${SQLITE3_INVOKER})
	endif()
endif()


# ffmpeg invoker

find_package(FFMPEG)
if (FFMPEG_FOUND)
	include_directories(${FFMPEG_INCLUDE_DIR})
	file(GLOB_RECURSE FFMPEG_INVOKER
		src/uscxml/plugins/invoker/ffmpeg/*.cpp
		src/uscxml/plugins/invoker/ffmpeg/*.h
	)
	source_group("Invoker\\ffmpeg" FILES ${FFMPEG_INVOKER})
	if (BUILD_AS_PLUGINS)
		add_library(
			invoker_ffmpeg SHARED 
			${FFMPEG_INVOKER})
		target_link_libraries(invoker_ffmpeg uscxml)
		set_target_properties(invoker_ffmpeg PROPERTIES FOLDER "Plugin Invoker")
	else()
		list (APPEND USCXML_FILES ${FFMPEG_INVOKER})
	endif()
endif()


# JavaScriptCore ecmascript datamodel
if (APPLE AND IOS AND OFF)
	FIND_LIBRARY(JSC_LIBRARY JavaScriptCore)
	set(JSC_FOUND ON)
	file(GLOB JSC_DATAMODEL
		src/uscxml/plugins/datamodel/ecmascript/JavaScriptCore/*.cpp
		src/uscxml/plugins/datamodel/ecmascript/JavaScriptCore/*.h
	)
	source_group("Datamodel\\jsc" FILES ${JSC_DATAMODEL})
	file(GLOB_RECURSE JSC_DOM
		src/uscxml/plugins/datamodel/ecmascript/JavaScriptCore/dom/*.cpp
		src/uscxml/plugins/datamodel/ecmascript/JavaScriptCore/dom/*.h
	)
	source_group("Datamodel\\DOM" FILES ${JSC_DOM})
	if (BUILD_AS_PLUGINS)
		add_library(
			datamodel_jsc SHARED 
			${JSC_DATAMODEL}
			${JSC_DOM})
		target_link_libraries(datamodel_jsc 
			uscxml
			${JSC_LIBRARY})
		set_target_properties(datamodel_jsc PROPERTIES FOLDER "Plugin DataModel")
	else()
		list (APPEND USCXML_FILES ${JSC_DATAMODEL})
		list (APPEND USCXML_FILES ${JSC_DOM})
		list (APPEND USCXML_OPT_LIBS ${JSC_LIBRARY})
	endif()

endif()


# NULL datamodel

file(GLOB NULL_DATAMODEL
	src/uscxml/plugins/datamodel/null/*.cpp
	src/uscxml/plugins/datamodel/null/*.h
)
source_group("Datamodel\\null" FILES ${NULL_DATAMODEL})
if (BUILD_AS_PLUGINS)
	add_library(datamodel_null SHARED ${NULL_DATAMODEL})
	target_link_libraries(datamodel_null uscxml)
	set_target_properties(datamodel_null PROPERTIES FOLDER "Plugin DataModel")
else()
	list (APPEND USCXML_FILES ${NULL_DATAMODEL})
endif()


# XPath datamodel

file(GLOB XPATH_DATAMODEL
	src/uscxml/plugins/datamodel/xpath/*.cpp
	src/uscxml/plugins/datamodel/xpath/*.h
)
source_group("Datamodel\\xpath" FILES ${XPATH_DATAMODEL})
if (BUILD_AS_PLUGINS)
	add_library(datamodel_xpath SHARED ${XPATH_DATAMODEL})
	target_link_libraries(datamodel_xpath uscxml)
	set_target_properties(datamodel_xpath PROPERTIES FOLDER "Plugin DataModel")
else()
	list (APPEND USCXML_FILES ${XPATH_DATAMODEL})
endif()


# GOOGLE V8 ecmascript datamodel

#if (NOT APPLE OR IOS)
	# set(ENV{V8_SRC} ${CMAKE_SOURCE_DIR}/../v8)
	find_package(V8)
	if (V8_FOUND)
		include_directories(${V8_INCLUDE_DIR})
		file(GLOB V8_DATAMODEL
			src/uscxml/plugins/datamodel/ecmascript/v8/*.cpp
			src/uscxml/plugins/datamodel/ecmascript/v8/*.h
		)
		source_group("Datamodel\\v8" FILES ${V8_DATAMODEL})
		file(GLOB_RECURSE V8_DOM
#			${PROJECT_SOURCE_DIR}/contrib/dom/scripts/gen/*.cpp
#			${PROJECT_SOURCE_DIR}/contrib/dom/scripts/gen/*.h
			src/uscxml/plugins/datamodel/ecmascript/v8/dom/*.cpp
			src/uscxml/plugins/datamodel/ecmascript/v8/dom/*.h
		)
		# include_directories(${PROJECT_SOURCE_DIR}/contrib/dom/scripts/gen/)
		# list(APPEND V8_DOM "src/uscxml/plugins/datamodel/ecmascript/v8/dom/V8DOM.cpp")
		# list(APPEND V8_DOM "src/uscxml/plugins/datamodel/ecmascript/v8/dom/V8DOM.h")
		
		source_group("Datamodel\\DOM" FILES ${V8_DOM})

		if (BUILD_AS_PLUGINS)
			add_library(
				datamodel_v8 SHARED 
				${V8_DATAMODEL}
				${V8_DOM})
			target_link_libraries(datamodel_v8 
				uscxml
				${V8_LIBRARY})
			set_target_properties(datamodel_v8 PROPERTIES FOLDER "Plugin DataModel")
		else()
			list (APPEND USCXML_FILES ${V8_DATAMODEL})
			list (APPEND USCXML_FILES ${V8_DOM})
			list (APPEND USCXML_OPT_LIBS ${V8_LIBRARY})
		endif()
	endif()
#endif()


# SWI PROLOG datamodel

#set(SWI_INCLUDE_HINT ${CMAKE_SOURCE_DIR}/../pl-devel/include)
#set(SWI_LIBRARY_HINT ${CMAKE_SOURCE_DIR}/../pl-devel/lib/x86_64-darwin12.2.0)
find_package(SWI)
#find_package(GMP)
#find_package(CURSES)
if (SWI_FOUND)
	include_directories(${SWI_INCLUDE_DIR})
#	include_directories(${GMP_INCLUDE_DIR})
#	include_directories(${CURSES_INCLUDE_DIR})
	file(GLOB_RECURSE SWI_DATAMODEL
		src/uscxml/plugins/datamodel/prolog/swi/*.cpp
		src/uscxml/plugins/datamodel/prolog/swi/*.h
	)
	source_group("Datamodel\\swi" FILES ${SWI_DATAMODEL})
	if (BUILD_AS_PLUGINS)
		add_library(
			datamodel_swi SHARED 
			${SWI_DATAMODEL})
		target_link_libraries(datamodel_swi 
			uscxml
#			${GMP_LIBRARY}
#			${CURSES_LIBRARIES}
			${SWI_LIBRARY})
		set_target_properties(datamodel_swi PROPERTIES FOLDER "Plugin DataModel")
	else()
		list (APPEND USCXML_FILES ${SWI_DATAMODEL})
		list (APPEND USCXML_OPT_LIBS ${SWI_LIBRARY}) # ${GMP_LIBRARY} ${CURSES_LIBRARIES})
	endif()
endif()


# UMUNDO invoker 

if (WIN32)
	find_package(UMUNDO COMPONENTS convenience)
else()
	find_package(UMUNDO COMPONENTS rpc serial core)
endif()
if (UMUNDO_FOUND)
	include_directories(${UMUNDO_INCLUDE_DIR})
	file(GLOB_RECURSE UMUNDO_INVOKER 
		src/uscxml/plugins/invoker/umundo/*.cpp 
		src/uscxml/plugins/invoker/umundo/*.h)
	source_group("Invoker\\umundo" FILES ${UMUNDO_INVOKER})
	if (BUILD_AS_PLUGINS)
		add_library(
			invoker_umundo SHARED 
			${UMUNDO_INVOKER})
		target_link_libraries(invoker_umundo 
			uscxml
			${UMUNDO_LIBRARIES})
		set_target_properties(invoker_umundo PROPERTIES FOLDER "Plugin Invoker")
	else()
		list (APPEND USCXML_FILES ${UMUNDO_INVOKER})
		list (APPEND USCXML_OPT_LIBS ${UMUNDO_LIBRARIES})
	endif()
	add_definitions("-DUMUNDO_STATIC")
endif()


# USCXML invoker 

file(GLOB_RECURSE USCXML_INVOKER 
	src/uscxml/plugins/invoker/scxml/*.cpp 
	src/uscxml/plugins/invoker/scxml/*.h)
source_group("Invoker\\uscxml" FILES ${USCXML_INVOKER})
if (BUILD_AS_PLUGINS)
	add_library(
		invoker_uscxml SHARED 
		${USCXML_INVOKER})
	target_link_libraries(invoker_uscxml 
		uscxml)
		set_target_properties(invoker_uscxml PROPERTIES FOLDER "Plugin Invoker")
else()
	list (APPEND USCXML_FILES ${USCXML_INVOKER})
endif()


# HTTP server invoker 

file(GLOB_RECURSE HTTPSERVLET_INVOKER 
	src/uscxml/plugins/invoker/http/*.cpp 
	src/uscxml/plugins/invoker/http/*.h)
source_group("Invoker\\httpservlet" FILES ${HTTPSERVLET_INVOKER})
if (BUILD_AS_PLUGINS)
	add_library(
		invoker_httpserver SHARED 
		${HTTPSERVLET_INVOKER})
	target_link_libraries(invoker_httpserver 
		uscxml)
		set_target_properties(invoker_httpserver PROPERTIES FOLDER "Plugin Invoker")
else()
	list (APPEND USCXML_FILES ${HTTPSERVLET_INVOKER})
endif()


# Heartbeat invoker

file(GLOB_RECURSE HEARTBEAT_INVOKER
	src/uscxml/plugins/invoker/heartbeat/*.cpp
	src/uscxml/plugins/invoker/heartbeat/*.h
)
source_group("Invoker\\heartbeat" FILES ${HEARTBEAT_INVOKER})
if (BUILD_AS_PLUGINS)
	add_library(
		invoker_heartbeat SHARED 
		${HEARTBEAT_INVOKER})
	target_link_libraries(invoker_heartbeat uscxml)
	set_target_properties(invoker_heartbeat PROPERTIES FOLDER "Plugin Invoker")
else()
	list (APPEND USCXML_FILES ${HEARTBEAT_INVOKER})
endif()


# OpenSceneGraph invoker
if (UNIX)
	set(CMAKE_FIND_LIBRARY_SUFFIXES ${CMAKE_FIND_LIBRARY_SUFFIXES_ORIG}) # link dynamically!
elseif(WIN32)
	if (ENV{OSG_ROOT} STREQUAL "")
		set(ENV{OSG_ROOT} "C:/Program Files/OpenSceneGraph-3.0.1")
	endif()
endif()

find_package(OpenSceneGraph COMPONENTS osgViewer osgGA osgText osgFX osgManipulator osgDB osgUtil OpenThreads)
find_package(OpenGL)
if (OPENSCENEGRAPH_FOUND AND OPENGL_FOUND)
	
	include_directories(${OPENSCENEGRAPH_INCLUDE_DIRS})
	include_directories(${OPENGL_INCLUDE_DIR})

	file(GLOB OPENSCENEGRAPH_INVOKER 
		src/uscxml/plugins/invoker/graphics/openscenegraph/*.cpp 
		src/uscxml/plugins/invoker/graphics/openscenegraph/*.h)
	source_group("Invoker\\scenegraph" FILES ${OPENSCENEGRAPH_INVOKER})

	if (BUILD_AS_PLUGINS)
		add_library(
			invoker_openscenegraph SHARED 
			${OPENSCENEGRAPH_INVOKER})
		target_link_libraries(invoker_openscenegraph
			${OPENSCENEGRAPH_LIBRARIES}
			${OPENGL_LIBRARIES}
			uscxml)
			set_target_properties(invoker_openscenegraph PROPERTIES FOLDER "Plugin Invoker")
	else()
		list (APPEND USCXML_FILES ${OPENSCENEGRAPH_INVOKER})
		list (APPEND USCXML_OPT_LIBS ${OPENSCENEGRAPH_LIBRARIES} ${OPENGL_LIBRARIES})
	endif()

	file(GLOB OPENSCENEGRAPH_CONVERTER_INVOKER 
		src/uscxml/plugins/invoker/graphics/openscenegraph/converter/*.cpp 
		src/uscxml/plugins/invoker/graphics/openscenegraph/converter/*.h)
	source_group("Invoker\\scenegraph\\convert" FILES ${OPENSCENEGRAPH_CONVERTER_INVOKER})

	if (BUILD_AS_PLUGINS)
		add_library(
			invoker_openscenegraph_convert SHARED 
			${OPENSCENEGRAPH_CONVERTER_INVOKER})
		target_link_libraries(invoker_openscenegraph_convert
			${OPENSCENEGRAPH_LIBRARIES}
			${OPENGL_LIBRARIES}
			uscxml)
			set_target_properties(invoker_openscenegraph_convert PROPERTIES FOLDER "Plugin Invoker")
	else()
		list (APPEND USCXML_FILES ${OPENSCENEGRAPH_CONVERTER_INVOKER})
		list (APPEND USCXML_OPT_LIBS ${OPENSCENEGRAPH_LIBRARIES} ${OPENGL_LIBRARIES})
	endif()

endif()

if (UNIX)
	set(CMAKE_FIND_LIBRARY_SUFFIXES .lib .a ${CMAKE_FIND_LIBRARY_SUFFIXES})
endif()

# MILES modality components

find_package(MILES)
if (MILES_FOUND)
  include_directories(${MILES_INCLUDE_DIR})

	# openal is only needed for miles
	find_package(OpenAL REQUIRED)
#	find_package(JPEG REQUIRED)
	list (APPEND MILES_LIBRARIES "iconv")
	list (APPEND MILES_LIBRARIES ${JPEG_LIBRARIES})
	include_directories(${OPENAL_INCLUDE_DIR})

  file(GLOB_RECURSE MILES_INVOKER src/uscxml/plugins/invoker/miles/*.cpp src/uscxml/plugins/invoker/miles/*.h)
	source_group("Invoker\\miles" FILES ${MILES_INVOKER})
#	message("MILES_INVOKER ${MILES_INVOKER}")

	if (BUILD_AS_PLUGINS)
		add_library(
			invoker_miles SHARED 
			${MILES_INVOKER})
		target_link_libraries(invoker_miles 
			${MILES_LIBRARIES}
			${OPENAL_LIBRARY}
			uscxml)
		set_target_properties(invoker_miles PROPERTIES FOLDER "Plugin Invoker")
	else()
  	list (APPEND USCXML_FILES ${MILES_INVOKER})
  	list (APPEND USCXML_OPT_LIBS ${MILES_LIBRARIES})
		list (APPEND USCXML_OPT_LIBS ${OPENAL_LIBRARY})
	endif()
endif()


# order of libraries matters with some gcc versions?!
if (UNIX AND NOT APPLE)
	list (APPEND USCXML_CORE_LIBS "pthread")
	list (APPEND USCXML_CORE_LIBS "rt")
	list (APPEND USCXML_CORE_LIBS "dl")
endif()

list(SORT USCXML_FILES)

############################################################
# Binaries and tests
############################################################

# build library
if (NOT BUILD_AS_PLUGINS)
	add_library(uscxml ${USCXML_FILES})
endif()
target_link_libraries(uscxml ${USCXML_OPT_LIBS} ${USCXML_CORE_LIBS})

add_executable(mmi-browser apps/mmi-browser.cpp ${PROJECT_SOURCE_DIR}/contrib/src/getopt/XGetopt.cpp)
target_link_libraries(mmi-browser uscxml)
set_target_properties(mmi-browser PROPERTIES FOLDER "Apps")
install_executable(TARGETS mmi-browser COMPONENT tools)

if (BUILD_TESTS)
	add_subdirectory(test)
endif()

if (NOT WIN32)
	add_subdirectory(src/bindings)
endif()

############################################################
# Header Files
############################################################

file(GLOB_RECURSE USCXML_HEADERS ${PROJECT_SOURCE_DIR}/src/*.h ${CMAKE_BINARY_DIR}/*.h)
INSTALL_HEADERS(HEADERS ${USCXML_HEADERS} COMPONENT headers)

############################################################
# Create config.h
############################################################

# determine path seperator to shorten filenames in Debug.cpp
if (WIN32)
    SET(PATH_SEPERATOR "\\\\")
else()
	SET(PATH_SEPERATOR "/")
endif()

# enable config.h style compile time options and add as "uscxml/config.h"
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/config.h.in ${CMAKE_CURRENT_BINARY_DIR}/uscxml/config.h)
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/contrib/ctest/CTestCustom.ctest.in ${CMAKE_CURRENT_BINARY_DIR}/CTestCustom.ctest @ONCE)

############################################################
# Installation / Provide package target
############################################################

# see contrib/cmake/CPackUSCXML.cmake
include(contrib/cmake/CPackUSCXML.cmake)

# This must always be last!
include(CPack)
