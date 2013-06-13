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
	OPTION(RUN_W3C_ECMA_TESTS "Run W3C ECMAScript tests" OFF)
	OPTION(RUN_W3C_XPATH_TESTS "Run W3C XPath tests" OFF)
endif()
OPTION(ENABLE_GCOV "Compile with gcov support" OFF)

OPTION(BUILD_DM_ECMA "Build with ECMAScript datamodel" ON)
OPTION(BUILD_DM_XPATH "Build with XPath datamodel" ON)
OPTION(BUILD_DM_PROLOG "Build with Prolog datamodel" ON)

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
set(USCXML_INCLUDE_DIRS)

# some compiler flags
#message("CMAKE_CXX_COMPILER_ID: ${CMAKE_CXX_COMPILER_ID}")

if(CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
	execute_process(COMMAND ${CMAKE_C_COMPILER} -dumpversion OUTPUT_VARIABLE GCC_VERSION)

	# best practices from scott meyers
	#	add_definitions(-Weffc++)

  # order of arguments of gcc matters again
#	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fPIC")
	add_definitions(-fPIC)
	add_definitions(-Wunreachable-code)

	if (CMAKE_BUILD_TYPE MATCHES ".*Deb.*" AND ENABLE_GCOV) # when not building for debug
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
elseif (CMAKE_CXX_COMPILER_ID STREQUAL "MSVC")
	add_definitions("-DZMQ_STATIC")
	add_definitions("-DPCRE_STATIC")
	add_definitions("-DUMUNDO_STATIC")
	add_definitions("-D_SCL_SECURE_NO_WARNINGS")
	add_definitions("-D_CRT_SECURE_NO_WARNINGS")
	add_definitions("/bigobj")
	
	# SET(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} /NODEFAULTLIB")
	# SET(CMAKE_EXE_LINKER_FLAGS_DEBUG "${CMAKE_EXE_LINKER_FLAGS_DEBUG} /NODEFAULTLIB:MSVCRTD.lib")
elseif (CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
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
set(CMAKE_FIND_LIBRARY_SUFFIXES_SHARED ${CMAKE_FIND_LIBRARY_SUFFIXES})
set(CMAKE_FIND_LIBRARY_SUFFIXES_STATIC .lib .a ${CMAKE_FIND_LIBRARY_SUFFIXES})

if(BUILD_PREFER_STATIC_LIBRARIES)
    SET(CMAKE_FIND_LIBRARY_SUFFIXES ${CMAKE_FIND_LIBRARY_SUFFIXES_STATIC})
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

OPTION(BUILD_AS_PLUGINS "Build invokers, ioprocessors and datamodels as plugins" OFF)

# this is where the config.h ends up
include_directories(${CMAKE_CURRENT_BINARY_DIR})
include_directories(src)

############################################################
# Dependent libraries
############################################################

if (NOT WIN32)
	# libxml2
	set(CMAKE_FIND_FRAMEWORK "LAST")
	find_package(LibXml2 REQUIRED)
	include_directories(${LIBXML2_INCLUDE_DIR})
	list (APPEND USCXML_CORE_LIBS ${LIBXML2_LIBRARIES})
	set(XML_LIBRARIES ${LIBXML2_LIBRARIES})
	list (APPEND USCXML_CORE_LIBS "dl")
	list (APPEND USCXML_CORE_LIBS "pthread")
elseif(WIN32)
	list (APPEND XML_LIBRARIES "Ws2_32")
	list (APPEND XML_LIBRARIES "Winmm")
	list (APPEND XML_LIBRARIES "Iphlpapi")
	list (APPEND XML_LIBRARIES "Netapi32")
	list (APPEND USCXML_CORE_LIBS ${XML_LIBRARIES})
endif()

# CURL
find_package(CURL REQUIRED)
include_directories(${CURL_INCLUDE_DIRS})
list (APPEND USCXML_CORE_LIBS ${CURL_LIBRARIES})
if (WIN32)
	add_definitions("-DCURL_STATICLIB")
endif()

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

#################################################
# Optional libraries

find_package(V8)
if (V8_FOUND)
	include_directories(${V8_INCLUDE_DIR})
	list (APPEND USCXML_OPT_LIBS ${V8_LIBRARY})
endif()

set(CMAKE_FIND_LIBRARY_SUFFIXES ${CMAKE_FIND_LIBRARY_SUFFIXES_SHARED})
find_package(SWI)
if (SWI_FOUND)
	include_directories(${SWI_INCLUDE_DIR})	
	if (BUILD_PREFER_STATIC_LIBRARIES)
		find_package(GMP)
		find_package(Curses)
		if (GMP_FOUND AND CURSES_FOUND)
			list (APPEND USCXML_OPT_LIBS ${SWI_LIBRARY} ${GMP_LIBRARY} ${CURSES_LIBRARIES})
		else()
			message("Not building datamodel with static SWI without NCurses and GMP")
			set(SWI_FOUND OFF)
		endif()
	else()
		list (APPEND USCXML_OPT_LIBS ${SWI_LIBRARY})
	endif()
endif()
set(CMAKE_FIND_LIBRARY_SUFFIXES ${CMAKE_FIND_LIBRARY_SUFFIXES_STATIC})

find_package(Sqlite3)
if (SQLITE3_FOUND)
endif()

find_package(FFMPEG)
if (FFMPEG_FOUND)
	include_directories (${FFMPEG_INCLUDE_DIR})		
endif()

if (WIN32)
	find_package(UMUNDO COMPONENTS convenience)
else()
	find_package(UMUNDO COMPONENTS rpc serial core)
endif()
if (UMUNDO_FOUND)
	include_directories (${UMUNDO_INCLUDE_DIR})
	list (APPEND USCXML_OPT_LIBS ${UMUNDO_LIBRARIES})
#	add_definitions("-DUMUNDO_STATIC")
endif()

if (UNIX)
	set(CMAKE_FIND_LIBRARY_SUFFIXES ${CMAKE_FIND_LIBRARY_SUFFIXES_SHARED}) # link dynamically!
elseif(WIN32)
	if (ENV{OSG_ROOT} STREQUAL "")
		set(ENV{OSG_ROOT} "C:/Program Files/OpenSceneGraph-3.0.1")
	endif()
endif()
find_package(OpenSceneGraph COMPONENTS osgViewer osgGA osgText osgFX osgManipulator osgDB osgUtil OpenThreads)
find_package(OpenGL)
if (OPENSCENEGRAPH_FOUND AND OPENGL_FOUND)	
	include_directories (${OPENSCENEGRAPH_INCLUDE_DIRS})
	include_directories (${OPENGL_INCLUDE_DIR})
	list (APPEND USCXML_OPT_LIBS ${OPENSCENEGRAPH_LIBRARIES} ${OPENGL_LIBRARIES})
endif()
if (UNIX)
	set(CMAKE_FIND_LIBRARY_SUFFIXES ${CMAKE_FIND_LIBRARY_SUFFIXES_STATIC})
endif()

find_package(MILES)
if (MILES_FOUND AND OFF)
	include_directories (${MILES_INCLUDE_DIR})
	list (APPEND USCXML_OPT_LIBS ${MILES_LIBRARIES})
	list (APPEND USCXML_OPT_LIBS ${OPENAL_LIBRARY})
endif()

set(CMAKE_FIND_LIBRARY_SUFFIXES ${CMAKE_FIND_LIBRARY_SUFFIXES_SHARED})
find_package(Protobuf)
if (PROTOBUF_FOUND)
	include_directories(${PROTOBUF_INCLUDE_DIRS})
	LIST(APPEND USCXML_OPT_LIBS optimized ${PROTOBUF_LIBRARY})
	LIST(APPEND USCXML_OPT_LIBS debug ${PROTOBUF_LIBRARY_DEBUG})
endif()
set(CMAKE_FIND_LIBRARY_SUFFIXES ${CMAKE_FIND_LIBRARY_SUFFIXES_STATIC})

#################################################
# Gather source files
#################################################

# we use include instead of add_subdirectory because
# source groups do not work otherwise.

add_subdirectory(src/uscxml)
include_directories(${USCXML_INCLUDE_DIRS})

if (UNIX AND NOT APPLE)
	list (APPEND USCXML_CORE_LIBS "rt")
endif()

############################################################
# Binaries and tests
############################################################

# we cannot use source groups in sub directories!
foreach( FILE ${USCXML_FILES} )
	get_filename_component(PATH ${FILE} PATH)
	
	if (${PATH} MATCHES ".*datamodel\\/ecmascript.*")
		STRING(REGEX MATCH "[^\\/]*$" COMP_NAME ${PATH})
		source_group("Datamodel\\EcmaScript\\${COMP_NAME}" FILES ${FILE})
	elseif (${PATH} MATCHES ".*datamodel\\/prolog.*")
		STRING(REGEX MATCH "[^\\/]*$" COMP_NAME ${PATH})
		source_group("Datamodel\\Prolog\\${COMP_NAME}" FILES ${FILE})
	elseif (${PATH} MATCHES ".*datamodel\\/xpath.*")
		source_group("Datamodel\\XPath" FILES ${FILE})
	elseif (${PATH} MATCHES ".*datamodel\\/null.*")
		source_group("Datamodel\\NULL" FILES ${FILE})
	
	elseif (${PATH} MATCHES ".*\\/invoker\\/.*")
		STRING(REGEX MATCH "[^\\/]*$" COMP_NAME ${PATH})
		source_group("Invoker\\${COMP_NAME}" FILES ${FILE})

	elseif (${PATH} MATCHES ".*\\/element\\/.*")
		STRING(REGEX MATCH "[^\\/]*$" COMP_NAME ${PATH})
		source_group("Element\\${COMP_NAME}" FILES ${FILE})

		elseif (${PATH} MATCHES ".*\\/ioprocessor\\/.*")
			STRING(REGEX MATCH "[^\\/]*$" COMP_NAME ${PATH})
			source_group("IOProcessor\\${COMP_NAME}" FILES ${FILE})

	else ()
		source_group(Interpreter FILES ${FILE})
	endif()
endforeach()

# build library
if (BUILD_AS_PLUGINS)
	add_library(uscxml ${USCXML_FILES})
	target_link_libraries(uscxml ${USCXML_CORE_LIBS})
else()
	add_library(uscxml ${USCXML_FILES})
	target_link_libraries(uscxml ${USCXML_OPT_LIBS} ${USCXML_CORE_LIBS})
endif()

add_executable(uscxml-browser apps/uscxml-browser.cpp ${PROJECT_SOURCE_DIR}/contrib/src/getopt/XGetopt.cpp)
target_link_libraries(uscxml-browser uscxml)
set_target_properties(uscxml-browser PROPERTIES FOLDER "Apps")
install_executable(TARGETS uscxml-browser COMPONENT tools)

if (PROTOBUF_FOUND)
	file(GLOB W3C-MMI-COMMON ${PROJECT_SOURCE_DIR}/apps/w3c-mmi/*.cpp ${PROJECT_SOURCE_DIR}/apps/w3c-mmi/*.h)

	file(GLOB_RECURSE W3C-MMI-IM ${PROJECT_SOURCE_DIR}/apps/w3c-mmi/im/*.cpp ${PROJECT_SOURCE_DIR}/apps/w3c-mmi/im/*.h)
	add_executable(uscxml-interaction-manager ${W3C-MMI-IM} ${W3C-MMI-COMMON})
	target_link_libraries(uscxml-interaction-manager uscxml)
	set_target_properties(uscxml-interaction-manager PROPERTIES FOLDER "Apps")
	install_executable(TARGETS uscxml-interaction-manager COMPONENT tools)

	file(GLOB_RECURSE W3C-MMI-MC ${PROJECT_SOURCE_DIR}/apps/w3c-mmi/mc/*.cpp ${PROJECT_SOURCE_DIR}/apps/w3c-mmi/mc/*.h)
	add_executable(uscxml-modality-component ${W3C-MMI-MC} ${W3C-MMI-COMMON})
	target_link_libraries(uscxml-modality-component uscxml)
	set_target_properties(uscxml-modality-component PROPERTIES FOLDER "Apps")
	install_executable(TARGETS uscxml-modality-component COMPONENT tools)
endif()

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
# Some concluding remarks
############################################################

message(STATUS "Linking against external:")
set(SKIP_NEXT OFF)
foreach(LIBRARY ${USCXML_OPT_LIBS})
	if (LIBRARY MATCHES "debug")
		if(CMAKE_BUILD_TYPE STREQUAL "Release")
			set(SKIP_NEXT ON)
		endif()
	elseif (LIBRARY MATCHES "optimized")
		if(CMAKE_BUILD_TYPE STREQUAL "Debug")
			set(SKIP_NEXT ON)
		endif()
	elseif (LIBRARY MATCHES "uscxml.*")
	elseif (LIBRARY MATCHES "mmi_proto.*")
	else()
		if (NOT SKIP_NEXT)
			message(STATUS "  ${LIBRARY}")
		else()
			set(SKIP_NEXT OFF)
		endif()
	endif()
endforeach()

set(AVAILABLE_DATAMODELS "")
set(ALL_FILES_STRING "${USCXML_FILES}")
if(ALL_FILES_STRING MATCHES ".*datamodel/ecmascript.*" OR TARGET datamodel_v8)
	set(AVAILABLE_DATAMODELS "ecmascript ${AVAILABLE_DATAMODELS}")
endif()
if(ALL_FILES_STRING MATCHES ".*datamodel/prolog.*" OR TARGET datamodel_swi)
	set(AVAILABLE_DATAMODELS "prolog ${AVAILABLE_DATAMODELS}")
endif()
if(ALL_FILES_STRING MATCHES ".*datamodel/xpath.*" OR TARGET datamodel_xpath)
	set(AVAILABLE_DATAMODELS "xpath ${AVAILABLE_DATAMODELS}")
endif()

set(AVAILABLE_LANGUAGE_BINDINGS "")
if (TARGET uscxmlNativePHP)
	set(AVAILABLE_LANGUAGE_BINDINGS "php ${AVAILABLE_LANGUAGE_BINDINGS}")
endif()

message(STATUS "Targets:")
message(STATUS "  Available datamodels ........... : null ${AVAILABLE_DATAMODELS}")
message(STATUS "  Available language bindings .... : ${AVAILABLE_LANGUAGE_BINDINGS}")
if (BUILD_SHARED_LIBS AND BUILD_BINDINGS)
	message(STATUS "")
	message(STATUS "    Warning: Building language bindings BUILD_SHARED_LIBS=ON")
	message(STATUS "             introduces runtime dependency to libumundocore")
	message(STATUS "")
endif()

message(STATUS "General information:")
message(STATUS "  Build type ..................... : ${CMAKE_BUILD_TYPE}")
if (BUILD_SHARED_LIBS)
	message(STATUS "  Building library as ............ : SHARED")
else()
	message(STATUS "  Building library as ............ : STATIC")
endif()

if (BUILD_PREFER_STATIC_LIBRARIES)
	message(STATUS "  Preferring dependent libraries . : STATIC ")
else()
	message(STATUS "  Preferring dependent libraries . : SHARED")
endif()

if (BUILD_PREFER_PREBUILT_LIBS)
	STRING(REGEX REPLACE "${PROJECT_SOURCE_DIR}/" "" REL_USCXML_PREBUILT_LIBRARY_PATH ${USCXML_PREBUILT_LIBRARY_PATH})
	message(STATUS "  Preferring dependent libraries . : from ${REL_USCXML_PREBUILT_LIBRARY_PATH}")
else()
	message(STATUS "  Preferring dependent libraries . : installed on system")
endif()

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

# This must always be last!
include(CPack)
