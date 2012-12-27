cmake_minimum_required(VERSION 2.8.4)

# specify USCXML version
SET(USCXML_VERSION_MAJOR "0")
SET(USCXML_VERSION_MINOR "0")
SET(USCXML_VERSION_PATCH "2")
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
	include_directories(${PROJECT_SOURCE_DIR}/contrib/snippets)
endif()

############################################################
# General setup
############################################################

# enable testing and actual output with tests
if (CMAKE_CROSSCOMPILING)
	OPTION(BUILD_TESTS "Build USCXML tests" OFF)
else()
	OPTION(BUILD_TESTS "Build USCXML tests" ON)
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

# some compiler flags
#message("CMAKE_CXX_COMPILER_ID: ${CMAKE_CXX_COMPILER_ID}")
if(${CMAKE_CXX_COMPILER_ID} STREQUAL "GNU")
	execute_process(COMMAND ${CMAKE_C_COMPILER} -dumpversion OUTPUT_VARIABLE GCC_VERSION)

	# best practices from scott meyers
	#	add_definitions(-Weffc++)

	set(CMAKE_CXX_FLAGS ${CMAKE_CXX_FLAGS} "-fPIC")
	
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
	add_definitions("-Wno-unused-value -Wno-unused-function -Wno-sign-compare")

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
	add_definitions("-Wno-parentheses-equality")
	set(CMAKE_CXX_FLAGS ${CMAKE_CXX_FLAGS} "-fPIC")
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

############################################################
# Dependent libraries
############################################################

set(USCXML_CORE_LIBS)
set(USCXML_OPT_LIBS)
set(USCXML_FILES)

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

# prefer rest as static libraries
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

find_package(Arabica REQUIRED)
include_directories(${ARABICA_INCLUDE_DIR})
list (APPEND USCXML_CORE_LIBS ${ARABICA_LIBRARY})
if (WIN32)
	add_definitions("-DUSE_MSXML")
endif()


# BOOST - header only

FIND_PATH(Boost_INCLUDE_DIR boost/version.hpp)
include_directories(${Boost_INCLUDE_DIR})


# CURL

find_package(CURL REQUIRED)
include_directories(${CURL_INCLUDE_DIRS})
list (APPEND USCXML_CORE_LIBS ${CURL_LIBRARIES})
if (WIN32)
	add_definitions("-DCURL_STATICLIB")
endif()


# LIBEVENT

#set(ENV{EVENT_SRC} ${CMAKE_SOURCE_DIR}/../libevent)
find_package(EVENT REQUIRED)
include_directories(${EVENT_INCLUDE_DIR})
list (APPEND USCXML_CORE_LIBS ${EVENT_LIBRARY})

############################################################
# Actual files of core library
############################################################

file(GLOB_RECURSE USCXML_CONCURRENCY
	src/uscxml/concurrency/*.cpp
	src/uscxml/concurrency/*.h
)
list (APPEND USCXML_FILES ${USCXML_CONCURRENCY})

file(GLOB_RECURSE USCXML_DEBUG
	src/uscxml/debug/*.cpp
	src/uscxml/debug/*.h
)
list (APPEND USCXML_FILES ${USCXML_DEBUG})

file(GLOB USCXML_CORE
	src/uscxml/*.cpp
	src/uscxml/*.h
)
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
	list (APPEND USCXML_FILES ${PLUMA})
	add_definitions("-DBUILD_AS_PLUGINS")
endif()

if (BUILD_AS_PLUGINS)
	add_library(uscxml ${USCXML_FILES})
endif()

#################################################
# optional libraries we can build as plugins

# LIBEVENT basichttp ioprocessor - this one is already required above

file(GLOB_RECURSE LIBEVENT_IOPROCESSOR
	src/uscxml/concurrency/*.cpp
	src/uscxml/concurrency/*.h
	src/uscxml/plugins/ioprocessor/basichttp/*.cpp
	src/uscxml/plugins/ioprocessor/basichttp/*.h
)
if (BUILD_AS_PLUGINS)
	add_library(
		ioprocessor_basichttp SHARED 
		${LIBEVENT_IOPROCESSOR})
	target_link_libraries(ioprocessor_basichttp uscxml)
	set_target_properties(ioprocessor_basichttp PROPERTIES FOLDER "Plugin IOProcessor")
else()
	list (APPEND USCXML_FILES ${LIBEVENT_IOPROCESSOR})
endif()


# GOOGLE V8 datamodel

# set(ENV{V8_SRC} ${CMAKE_SOURCE_DIR}/../v8)
find_package(V8)
if (V8_FOUND)
	include_directories(${V8_INCLUDE_DIR})
	file(GLOB_RECURSE V8_DATAMODEL
		src/uscxml/plugins/datamodel/ecmascript/v8/*.cpp
		src/uscxml/plugins/datamodel/ecmascript/v8/*.h
	)
	if (BUILD_AS_PLUGINS)
		add_library(
			datamodel_v8 SHARED 
			${V8_DATAMODEL})
		target_link_libraries(datamodel_v8 
			uscxml
			${V8_LIBRARY})
		set_target_properties(datamodel_v8 PROPERTIES FOLDER "Plugin DataModel")
	else()
		list (APPEND USCXML_FILES ${V8_DATAMODEL})
		list (APPEND USCXML_OPT_LIBS ${V8_LIBRARY})
	endif()
endif()


# SWI PROLOG datamodel

# set(ENV{V8_SRC} ${CMAKE_SOURCE_DIR}/../v8)
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
endif()
add_definitions("-DUMUNDO_STATIC")


# USCXML invoker 

file(GLOB_RECURSE USCXML_INVOKER 
	src/uscxml/plugins/invoker/scxml/*.cpp 
	src/uscxml/plugins/invoker/scxml/*.h)
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


# OpenSceneGraph invoker

find_package(OpenSceneGraph COMPONENTS osgDB osgGA osgUtil osgText osgFX osgManipulator osgViewer OpenThreads)
if (OPENSCENEGRAPH_FOUND)
	include_directories(${OPENSCENEGRAPH_INCLUDE_DIRS})
	file(GLOB_RECURSE OPENSCENEGRAPH_INVOKER 
		src/uscxml/plugins/invoker/graphics/openscenegraph/*.cpp 
		src/uscxml/plugins/invoker/graphics/openscenegraph/*.h)
	if (BUILD_AS_PLUGINS)
		add_library(
			invoker_openscenegraph SHARED 
			${OPENSCENEGRAPH_INVOKER})
		target_link_libraries(invoker_openscenegraph
			${OPENSCENEGRAPH_LIBRARIES}
			uscxml)
			set_target_properties(invoker_openscenegraph PROPERTIES FOLDER "Plugin Invoker")
	else()
		list (APPEND USCXML_FILES ${OPENSCENEGRAPH_INVOKER})
		list (APPEND USCXML_OPT_LIBS ${OPENSCENEGRAPH_LIBRARIES})
	endif()

endif()


# MILES modality components

#find_package(MILES COMPONENTS core audio debug)
if (MILES_FOUND AND OFF)
  include_directories(${MILES_INCLUDE_DIR})

	# openal is only needed for miles
	find_package(OpenAL REQUIRED)
	include_directories(${OPENAL_INCLUDE_DIR})

  file(GLOB_RECURSE MILES_INVOKER src/uscxml/invoker/modality/miles/*.cpp src/uscxml/invoker/modality/miles/*.h)
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
endif()

############################################################
# Binaries and tests
############################################################

# build library
if (NOT BUILD_AS_PLUGINS)
	add_library(uscxml ${USCXML_FILES})
endif()
target_link_libraries(uscxml ${USCXML_OPT_LIBS} ${USCXML_CORE_LIBS})

add_executable(mmi-browser apps/mmi-browser.cpp ${PROJECT_SOURCE_DIR}/contrib/snippets/XGetopt.cpp)
target_link_libraries(mmi-browser uscxml)
set_target_properties(mmi-browser PROPERTIES FOLDER "Apps")
install_executable(TARGETS mmi-browser COMPONENT tools)

if (BUILD_TESTS)
	add_subdirectory(test)
endif()

add_subdirectory(src/bindings)

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
include_directories(${CMAKE_CURRENT_BINARY_DIR})

############################################################
# Header Files
############################################################

file(GLOB_RECURSE USCXML_HEADERS ${PROJECT_SOURCE_DIR}/src/*.h ${CMAKE_BINARY_DIR}/*.h)
INSTALL_HEADERS(HEADERS ${USCXML_HEADERS} COMPONENT headers)

############################################################
# Installation / Provide package target
############################################################

# see contrib/cmake/CPackUSCXML.cmake
include(contrib/cmake/CPackUSCXML.cmake)

# This must always be last!
include(CPack)
