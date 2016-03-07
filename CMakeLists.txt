cmake_minimum_required(VERSION 2.8.4)

# TODO:
# - Have a look at PGO:
# https://mailman.videolan.org/pipermail/x265-devel/2015-April/007399.html

cmake_policy(PUSH)
if(POLICY CMP0042)
	# new behavior defaults to ON for MACOSX_RPATH
	cmake_policy(SET CMP0042 NEW)
endif()
if(POLICY CMP0045)
	# Error on non-existent target in get_target_property, 
	# set to old as we actually use it to check for specific targets
	cmake_policy(SET CMP0045 OLD)
endif()
if(POLICY CMP0046)
	# Error on non-existent dependency in add_dependencies
	cmake_policy(SET CMP0046 NEW)
endif()
if(POLICY CMP0054)
	# Escape variables in if
	cmake_policy(SET CMP0054 OLD)
endif()
if(POLICY CMP0059)
	# Don't treat ``DEFINITIONS`` as a built-in directory property - required for cotire
	cmake_policy(SET CMP0059 OLD)
endif()

# specify USCXML version
SET(USCXML_VERSION_MAJOR "0")
SET(USCXML_VERSION_MINOR "4")
SET(USCXML_VERSION_PATCH "0")
SET(USCXML_VERSION ${USCXML_VERSION_MAJOR}.${USCXML_VERSION_MINOR}.${USCXML_VERSION_PATCH})

# build type has to be set before the project definition
SET(BUILD_TYPE_HELP "Choose the type of build, options are: None(CMAKE_CXX_FLAGS or CMAKE_C_FLAGS used) Debug, Release, RelWithDebInfo, MinSizeRel.")
IF(DEFINED CMAKE_BUILD_TYPE)
   SET(CMAKE_BUILD_TYPE ${CMAKE_BUILD_TYPE} CACHE STRING ${BUILD_TYPE_HELP})
ELSE()
   SET(CMAKE_BUILD_TYPE Release CACHE STRING ${BUILD_TYPE_HELP})
ENDIF()

project(uscxml)

# where to find the cmake modules we distribute
set(CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/contrib/cmake)
include("${CMAKE_MODULE_PATH}/USCXMLMacros.cmake")
include("${CMAKE_MODULE_PATH}/FunctionExists.cmake")
include("${CMAKE_MODULE_PATH}/HeaderExists.cmake")
include("${CMAKE_MODULE_PATH}/BinaryExists.cmake")
include("${CMAKE_MODULE_PATH}/TryCompile.cmake")

# CMake 2.8.11 reports AMD64 for Windows 64Bit, where earlier versions reported x86
# we resolve it with a 64bit check later
if (${CMAKE_SYSTEM_PROCESSOR} STREQUAL "AMD64")
  set(CMAKE_SYSTEM_PROCESSOR "x86")
endif()
if (${CMAKE_SYSTEM_PROCESSOR} STREQUAL "i386")
  set(CMAKE_SYSTEM_PROCESSOR "x86")
endif()
if (${CMAKE_SYSTEM_PROCESSOR} STREQUAL "x86_64")
  set(CMAKE_SYSTEM_PROCESSOR "x86")
endif()

# use folders in the IDEs for the various targets (e.g. Library, Testing, Tools ..)
set_property(GLOBAL PROPERTY USE_FOLDERS ON)

# lower case version of system name and compiler for library paths
string(TOLOWER ${CMAKE_SYSTEM_NAME} CMAKE_SYSTEM_NAME_LC)
string(TOLOWER ${CMAKE_CXX_COMPILER_ID} CMAKE_CXX_COMPILER_ID_LC)

if (WIN32)
	set(CMAKE_CXX_COMPILER_ID_LC ${CMAKE_CXX_COMPILER_ID_LC}${MSVC_VERSION})
endif()

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
	set(64BIT_SUFFIX "_64")
	# additional library paths to be searched
	set(FIND_LIBRARY_USE_LIB64_PATHS ON)
# 	LIST(APPEND CMAKE_FIND_ROOT_PATH "/usr/local/lib64")
# 	LIST(APPEND CMAKE_FIND_ROOT_PATH "/usr/lib64")
endif()

if (APPLE)
	set(LIBCPP_NAME "libstdc++") # before mavericks
	# get MacOSX version
	execute_process(COMMAND /usr/bin/sw_vers -productVersion
		OUTPUT_VARIABLE MACOSX_VERSION
		ERROR_VARIABLE MACOSX_VERSION_errors
		RESULT_VARIABLE MACOSX_VERSION_result
	OUTPUT_STRIP_TRAILING_WHITESPACE)
	if (MACOSX_VERSION)
		THREE_PART_VERSION_TO_VARS(
			${MACOSX_VERSION}
			MACOSX_VERSION_MAJOR 
			MACOSX_VERSION_MINOR 
			MACOSX_VERSION_PATCH)
	endif()
	if (MACOSX_VERSION VERSION_GREATER "10.8.99")
		set(LIBCPP_NAME "libc++") # mavericks
		# LIST(APPEND CMAKE_FIND_ROOT_PATH ${CMAKE_OSX_SYSROOT})
		# make sure that we find libxml2 here first
		set(CMAKE_FIND_ROOT_PATH ${CMAKE_OSX_SYSROOT} ${CMAKE_FIND_ROOT_PATH})
	endif()
endif()

if (NOT $ENV{MACOSX_DEPLOYMENT_TARGET} STREQUAL "" 
    AND ENV{MACOSX_DEPLOYMENT_TARGET} VERSION_LESS "10.9" 
    AND MACOSX_VERSION VERSION_GREATER "10.8.99")
  message(WARNING "\nMACOSX_DEPLOYMENT_TARGET is set to $ENV{MACOSX_DEPLOYMENT_TARGET} implying libstdc++ instead of libc++ - linking against prebuilts from 10.8")
  set(MACOSX_VERSION_MINOR 8)
endif()

# We use the toolchain file from http://code.google.com/p/android-cmake/
if (CMAKE_CROSSCOMPILING AND ANDROID_ABI)
	set(ANDROID ON)
	set(CMAKE_CROSSCOMPILING_TARGET android)
	set(CMAKE_SYSTEM_VERSION ${ANDROID_NATIVE_API_LEVEL})
endif()

if (CMAKE_CROSSCOMPILING)
	if (IOS)
		add_definitions(-DTARGET_OS_IPHONE)
	elseif(IOSSIM)
		add_definitions(-DTARGET_IPHONE_SIMULATOR)
	endif()
endif()

#
# Setting the CMAKE_FIND_ROOT_PATH to a list of directories will cause all CMake modules
# to look in these directories in addition to the system search paths:
# http://www.vtk.org/Wiki/CMake_Cross_Compiling#Searching_and_finding_external_software
#


#
# determine platform id
#
SET(USCXML_PLATFORM_ID)
if (CMAKE_SYSTEM_NAME_LC)
	set(USCXML_PLATFORM_ID ${CMAKE_SYSTEM_NAME_LC})
else()
	set(USCXML_PLATFORM_ID "unknown")
endif()

if (CMAKE_SYSTEM_PROCESSOR)
	set(USCXML_PLATFORM_ID "${USCXML_PLATFORM_ID}-${CMAKE_SYSTEM_PROCESSOR}${64BIT_SUFFIX}")
else()
	set(USCXML_PLATFORM_ID "unknown")
endif()

if (CMAKE_CXX_COMPILER_ID_LC)
	set(USCXML_PLATFORM_ID "${USCXML_PLATFORM_ID}-${CMAKE_CXX_COMPILER_ID_LC}")
endif()

if (LIBCPP_NAME)
	set(USCXML_PLATFORM_ID "${USCXML_PLATFORM_ID}-${LIBCPP_NAME}")
endif()

# handle cross compiles
if (CMAKE_CROSSCOMPILING)
	if (IOS)
		SET(USCXML_PLATFORM_ID "ios-arm-clang")
		SET(CMAKE_FIND_ROOT_PATH_MODE_LIBRARY "ONLY")
	elseif (ANDROID)
		# handle mips, x86 and arm
		SET(USCXML_PLATFORM_ID "android-${ANDROID_ABI}")
		
		SET(CMAKE_FIND_ROOT_PATH_MODE_LIBRARY "ONLY") # we need both to find jni - we don't?
		SET(CMAKE_FIND_ROOT_PATH_MODE_PROGRAM "BOTH")
		SET(CMAKE_FIND_ROOT_PATH_MODE_INCLUDE "BOTH")
		
		LIST(APPEND CMAKE_PREFIX_PATH "/usr/local/bin") # this is needed to find swig
		LIST(APPEND CMAKE_PREFIX_PATH "/opt/local/bin") # this is needed to find protoc
	endif()
endif()

SET(USCXML_PREBUILT_LIBRARY_PATH)
SET(USCXML_PREBUILT_HEADER_PATH  "${PROJECT_SOURCE_DIR}/contrib/prebuilt")
SET(USCXML_PREBUILT_LIBRARY_PATH "${PROJECT_SOURCE_DIR}/contrib/prebuilt/${USCXML_PLATFORM_ID}")

SET(USCXML_LIBRARY_HOST_URL_PREFIX "http://uscxml.tk.informatik.tu-darmstadt.de/prebuilt" CACHE STRING "The root path of an URL where to look for prebuilt libraries." FORCE)
SET(USCXML_LIBRARY_ARCHIVE_NAME "uscxml-prebuilt-${USCXML_PLATFORM_ID}.tgz")

#
# Download platform independent headers
#

# delete if too old or unversioned
if (EXISTS "${PROJECT_SOURCE_DIR}/contrib/prebuilt/include/VERSION.txt")
	file (STRINGS "${PROJECT_SOURCE_DIR}/contrib/prebuilt/include/VERSION.txt" PREBUILT_INCUDES_VERSION)
endif()
if (NOT "${USCXML_VERSION}" VERSION_EQUAL "${PREBUILT_INCUDES_VERSION}")
	message(STATUS "Prebuilt headers unversioned, too old or non-existent - deleting and downloading again")
	execute_process(
		COMMAND ${CMAKE_COMMAND} -E remove_directory ${PROJECT_SOURCE_DIR}/contrib/prebuilt/include
	)
endif()

# download if not existing
if (NOT EXISTS ${PROJECT_SOURCE_DIR}/contrib/prebuilt/include)
	message(STATUS "Downloading ${USCXML_LIBRARY_HOST_URL_PREFIX}/${USCXML_VERSION}/include.tgz")

	file(
		DOWNLOAD 
			${USCXML_LIBRARY_HOST_URL_PREFIX}/${USCXML_VERSION}/include.tgz
			${PROJECT_SOURCE_DIR}/contrib/prebuilt/include.tgz
		INACTIVITY_TIMEOUT 60 
		STATUS DOWNLOAD_STATUS 
		SHOW_PROGRESS)
		
	list(GET DOWNLOAD_STATUS 0 STATUS_CODE)
	list(GET DOWNLOAD_STATUS 1 STATUS_STRING)
	if(STATUS_CODE EQUAL 0)
		execute_process(
			COMMAND ${CMAKE_COMMAND} -E tar xzf ${PROJECT_SOURCE_DIR}/contrib/prebuilt/include.tgz
			WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}/contrib/prebuilt/
		)
		execute_process(
			COMMAND ${CMAKE_COMMAND} -E remove ${PROJECT_SOURCE_DIR}/contrib/prebuilt/include.tgz
			WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}/contrib/prebuilt/
		)
		file(WRITE ${PROJECT_SOURCE_DIR}/contrib/prebuilt/include/VERSION.txt "${USCXML_VERSION}")
	else()
		message(FATAL_ERROR "\nDownloading header files\nFAILED with ${STATUS_STRING} (${STATUS_CODE}) \nThis should not happen, retry?")
	endif()
endif()

#
# Download platform dependent headers and libraries
#

# only delete if too old
if (EXISTS "${PROJECT_SOURCE_DIR}/contrib/prebuilt/${USCXML_PLATFORM_ID}/VERSION.txt")
	file (STRINGS "${PROJECT_SOURCE_DIR}/contrib/prebuilt/${USCXML_PLATFORM_ID}/VERSION.txt" PREBUILT_LIBRARIES_VERSION)
	if (NOT "${USCXML_VERSION}" VERSION_EQUAL "${PREBUILT_LIBRARIES_VERSION}")
		message(STATUS "Prebuilt libraries unversioned, too old or non-existent - deleting and downloading again")
		execute_process(
			COMMAND ${CMAKE_COMMAND} -E remove_directory ${PROJECT_SOURCE_DIR}/contrib/prebuilt/${USCXML_PLATFORM_ID}
		)
	endif()
endif()


if (NOT EXISTS ${USCXML_PREBUILT_LIBRARY_PATH})
	message(STATUS "Cannot find prebuilt libraries in ${USCXML_PREBUILT_LIBRARY_PATH}")
	message(STATUS "Trying to download ${USCXML_LIBRARY_HOST_URL_PREFIX}/${USCXML_VERSION}/${USCXML_LIBRARY_ARCHIVE_NAME}")
	file(
		DOWNLOAD 
			${USCXML_LIBRARY_HOST_URL_PREFIX}/${USCXML_VERSION}/${USCXML_LIBRARY_ARCHIVE_NAME}
			${PROJECT_SOURCE_DIR}/contrib/prebuilt/${USCXML_LIBRARY_ARCHIVE_NAME}
		INACTIVITY_TIMEOUT 60 
		STATUS DOWNLOAD_STATUS 
		SHOW_PROGRESS)
	
	list(GET DOWNLOAD_STATUS 0 STATUS_CODE)
	list(GET DOWNLOAD_STATUS 1 STATUS_STRING)
	if(STATUS_CODE EQUAL 0)
		# everything worked out fine! - create dir, unpack and delete
		file(MAKE_DIRECTORY ${PROJECT_SOURCE_DIR}/contrib/prebuilt/${USCXML_PLATFORM_ID})
		execute_process(
			COMMAND ${CMAKE_COMMAND} -E tar xzf ${PROJECT_SOURCE_DIR}/contrib/prebuilt/${USCXML_LIBRARY_ARCHIVE_NAME}
			WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}/contrib/prebuilt/${USCXML_PLATFORM_ID}
		)
		execute_process(
			COMMAND ${CMAKE_COMMAND} -E remove ${PROJECT_SOURCE_DIR}/contrib/prebuilt/${USCXML_LIBRARY_ARCHIVE_NAME}
			WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}/contrib/prebuilt/
		)
		file(WRITE ${PROJECT_SOURCE_DIR}/contrib/prebuilt/${USCXML_PLATFORM_ID}/VERSION.txt "${USCXML_VERSION}")
	elseif(
		NOT STATUS_CODE EQUAL 19 AND   # FTP: Invalid file / file not found
		NOT STATUS_CODE EQUAL 22)      # HTTP: HTTP response code
		# server was unreachable, do not create dir to retry
		message(FATAL_ERROR "\nDownloading prebuilt libraries\nFAILED with ${STATUS_STRING} (${STATUS_CODE}) \nThis should not happen, retry?")
	else()
		# we did not know the file, create dir for manual libs
		file(MAKE_DIRECTORY ${PROJECT_SOURCE_DIR}/contrib/prebuilt/${USCXML_PLATFORM_ID})
		execute_process(
			COMMAND ${CMAKE_COMMAND} -E remove ${PROJECT_SOURCE_DIR}/contrib/prebuilt/${USCXML_LIBRARY_ARCHIVE_NAME}
			WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}/contrib/prebuilt/
		)
		message(FATAL_ERROR "\nPlatform is not supported!\nProvide headers and libraries in\n${PROJECT_SOURCE_DIR}/contrib/prebuilt/${USCXML_PLATFORM_ID}/")
	endif()
endif()

if (CMAKE_CROSSCOMPILING)
	OPTION(BUILD_SHARED_LIBS "Build shared libraries" OFF)
	OPTION(ENABLE_COTIRE "Enable compile time reduction techniques" OFF)
else()
	OPTION(BUILD_SHARED_LIBS "Build shared libraries" ON)
endif()

if (${CMAKE_CXX_COMPILER_ID} STREQUAL "MSVC")
	OPTION(ENABLE_COTIRE "Enable compile time reduction techniques" OFF)
else()
	OPTION(ENABLE_COTIRE "Enable compile time reduction techniques" ON)
endif()

if (NOT BUILD_SHARED_LIBS)
	add_definitions("-DUSCXML_STATIC")
endif()

#
# BUILD_PREFER_PREBUILT_LIBS:
# Do we want to search system paths or contrib/prebuilt first?
#
if (CMAKE_CROSSCOMPILING)
	# always prefer prebuilt libraries for cross-compiling
	OPTION(BUILD_PREFER_PREBUILT_LIBS "Search libraries in contrib/prebuilt first" ON)
	SET(CMAKE_PREFIX_PATH "${USCXML_PREBUILT_LIBRARY_PATH};${USCXML_PREBUILT_HEADER_PATH};${CMAKE_PREFIX_PATH}")
else()
	OPTION(BUILD_PREFER_PREBUILT_LIBS "Search libraries in contrib/prebuilt first" ON)
	if (BUILD_PREFER_PREBUILT_LIBS)
		# for everything, we start our search in contrib/prebuilt
		SET(CMAKE_PREFIX_PATH "${USCXML_PREBUILT_LIBRARY_PATH};${USCXML_PREBUILT_HEADER_PATH};${CMAKE_PREFIX_PATH}")
	else()
		# using this trick, we search paths from find_* before CMAKE_FIND_ROOT_PATH as '/' is prepended first
		SET(CMAKE_PREFIX_PATH "/;${CMAKE_PREFIX_PATH};${USCXML_PREBUILT_LIBRARY_PATH};${USCXML_PREBUILT_HEADER_PATH}")
	endif()
endif()
include_directories(${USCXML_PREBUILT_LIBRARY_PATH}/include)

if (CMAKE_CROSSCOMPILING)
	set(CMAKE_FIND_ROOT_PATH ${CMAKE_FIND_ROOT_PATH} ${CMAKE_PREFIX_PATH})
endif()
# message(STATUS "CMAKE_FIND_ROOT_PATH: ${CMAKE_FIND_ROOT_PATH}")
# message(STATUS "CMAKE_PREFIX_PATH   : ${CMAKE_PREFIX_PATH}")
# message(FATAL_ERROR "")

if (WIN32)
	set(BUILD_SHARED_LIBS OFF)
	include_directories(${PROJECT_SOURCE_DIR}/contrib/src/getopt)
	include_directories(${PROJECT_SOURCE_DIR}/contrib/src/inttypes)
endif()
include_directories(${PROJECT_SOURCE_DIR}/contrib/src/jsmn)
include_directories(${PROJECT_SOURCE_DIR}/contrib/src/evws)
#include_directories(${PROJECT_SOURCE_DIR}/contrib/src/google-url)

############################################################
# General setup
############################################################

# enable testing and actual output with tests
if (CMAKE_CROSSCOMPILING)
	OPTION(BUILD_TESTS "Build USCXML tests" OFF)
else()
	OPTION(BUILD_TESTS "Build USCXML tests" ON)
	OPTION(BUILD_TESTS_W3C_ECMA "Create W3C ECMAScript tests" ON)
	OPTION(BUILD_TESTS_W3C_XPATH "Create W3C XPath tests" ON)
	OPTION(BUILD_TESTS_W3C_LUA "Create W3C Lua tests" ON)
	OPTION(BUILD_TESTS_W3C_PROLOG "Create W3C Prolog tests" ON)
	OPTION(BUILD_TESTS_W3C_PROMELA "Create W3C Promela tests" ON)
	
	OPTION(BUILD_TESTS_FSM "Build FSM converted W3C tests" OFF)
	OPTION(BUILD_TESTS_FSM_ECMA "Create FSM converted W3C ECMAScript tests" ON)
	OPTION(BUILD_TESTS_FSM_XPATH "Create FSM converted W3C XPath tests" ON)
	OPTION(BUILD_TESTS_FSM_LUA "Create FSM converted W3C Lua tests" ON)
	OPTION(BUILD_TESTS_FSM_PROLOG "Create FSM converted W3C Prolog tests" ON)
	OPTION(BUILD_TESTS_FSM_PROMELA "Create FSM converted W3C Promela tests" ON)
	OPTION(BUILD_TESTS_GENERATED_C "Create tests for generated C machines" ON)

endif()
OPTION(ENABLE_GCOV "Compile with gcov support" OFF)

OPTION(BUILD_PROFILING "Build with profiling information" OFF)
OPTION(BUILD_MINIMAL "Build only features mandated by specification" OFF)
OPTION(BUILD_DM_ECMA "Build with ECMAScript datamodel" ON)
OPTION(BUILD_DM_XPATH "Build with XPath datamodel" ON)
OPTION(BUILD_DM_PROLOG "Build with Prolog datamodel" ON)
OPTION(BUILD_DM_PROMELA "Build with Promela datamodel" ON)
OPTION(BUILD_DM_LUA "Build with Lua datamodel" ON)

OPTION(BUILD_BINDING_JAVA "Build language bindings for Java" ON)
OPTION(BUILD_BINDING_CSHARP "Build language bindings for CSharp" ON)
OPTION(BUILD_BINDING_PHP "Build language bindings for PHP" OFF)

# ccache:
# http://stackoverflow.com/questions/1815688/how-to-use-ccache-with-cmake
#
# see also:
# http://blogs.s-osg.org/a-conclusion-to-accelerating-your-build-with-clang/

find_program(CCACHE_FOUND ccache)
if(CCACHE_FOUND)
    set_property(GLOBAL PROPERTY RULE_LAUNCH_COMPILE ccache)
    set_property(GLOBAL PROPERTY RULE_LAUNCH_LINK ccache)
endif(CCACHE_FOUND)


# a dummy target to depend on the targets needed for tests, see:
# http://stackoverflow.com/questions/733475/cmake-ctest-make-test-doesnt-build-tests
add_custom_target(ALL_TESTS COMMENT "Building all tests when BUILD_TESTS is enabled")
if (BUILD_TESTS)
	enable_testing()
	SET(ENV{CTEST_OUTPUT_ON_FAILURE} ON)
endif()

OPTION(DIST_PREPARE "Put libraries into the lib folder of the source tree" OFF)

# we need USCXML_CORE_LIBS here for -lgcov
set(USCXML_CORE_LIBS)
set(USCXML_OPT_LIBS)
set(USCXML_FILES)
set(USCXML_TRANSFORM_FILES)
set(USCXML_INCLUDE_DIRS)

# some compiler flags
#message("CMAKE_CXX_COMPILER_ID: ${CMAKE_CXX_COMPILER_ID}")

if(${CMAKE_CXX_COMPILER_ID} STREQUAL "GNU")
	execute_process(COMMAND ${CMAKE_C_COMPILER} -dumpversion OUTPUT_VARIABLE GCC_VERSION)

	# best practices from scott meyers
	#	add_definitions(-Weffc++)

  # order of arguments of gcc matters again
#	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fPIC")
	add_definitions(-fPIC)
	#add_definitions(-Wunreachable-code)

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
	add_definitions(-Wno-unused-variable)

	# we cannot tread warning as error with the "narrowing problem"
	# add_definitions(-Werror)

	if(GCC_VERSION VERSION_EQUAL 4.7 OR GCC_VERSION VERSION_GREATER 4.7)
		# when compiling as C++11, narrowing is a warning but older compilers complain about the option
		add_definitions(-Wno-narrowing)
	endif()

	if(GCC_VERSION VERSION_EQUAL 4.8 OR GCC_VERSION VERSION_GREATER 4.8)
		add_definitions(-Wno-unused-local-typedefs)
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

	# set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} /GL") # /LTCG is implied with /GL.

	# be very clear about linking debug / non-debug C++ runtimes
	foreach(FLAGS CMAKE_EXE_LINKER_FLAGS_RELEASE CMAKE_SHARED_LINKER_FLAGS_RELEASE CMAKE_MODULE_LINKER_FLAGS_RELEASE)
		set(${FLAGS} "${${FLAGS}} /ignore:4099 /NODEFAULTLIB:MSVCRTD")
	endforeach()

	# use static MSVCRT
	# if (NOT BUILD_AS_PLUGINS)
	# 	foreach(FLAGS 
	# 		CMAKE_C_FLAGS
	# 		CMAKE_CXX_FLAGS
	# 		CMAKE_C_FLAGS_DEBUG
	# 		CMAKE_C_FLAGS_MINSIZEREL
	# 		CMAKE_C_FLAGS_RELEASE
	# 		CMAKE_C_FLAGS_RELWITHDEBINFO
	# 		CMAKE_CXX_FLAGS_DEBUG
	# 		CMAKE_CXX_FLAGS_MINSIZEREL
	# 		CMAKE_CXX_FLAGS_RELEASE
	# 		CMAKE_CXX_FLAGS_RELWITHDEBINFO)
	# 		if(${FLAGS} MATCHES "/MD")
	# 			string(REGEX REPLACE "/MD" "/MT" ${FLAGS} "${${FLAGS}}")
	# 		endif()
	# 	endforeach()
	# endif()
	
elseif (${CMAKE_CXX_COMPILER_ID} STREQUAL "Clang")
	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wno-parentheses-equality")
	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wno-string-plus-int")
	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wno-non-literal-null-conversion")
	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wno-null-conversion")
	
	# clang throws these for boost all over the place!
	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wno-unused-local-typedefs")
	
	#SET(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -stdlib=libstdc++")
	
	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fPIC")
	# set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -read_only_relocs suppress")
	# set(CMAKE_EXE_LINKER_FLAGS_DEBUG "${CMAKE_EXE_LINKER_FLAGS_DEBUG} -read_only_relocs suppress")

	# not too sure when this happened, 'void' has to be qualified as 'std::type_info' on __cxa_throw
	if(CMAKE_CXX_COMPILER_VERSION VERSION_EQUAL 4.3 OR CMAKE_CXX_COMPILER_VERSION VERSION_GREATER 4.3)
		set(CXA_THROW_TYPEINFO_SIGNATURE ON)
	endif()
	
else()
	message(FATAL_ERROR "Unknown compiler: ${CMAKE_CXX_COMPILER_ID}")
endif()

set(CMAKE_COMPILER_STRING "${CMAKE_CXX_COMPILER_ID} ${CMAKE_CXX_COMPILER_VERSION}")

if (APPLE)
#	set(CMAKE_OSX_ARCHITECTURES "i386;x86_64")
endif()

# see http://www.mail-archive.com/cmake@cmake.org/msg23240.html
if (APPLE)
	if (MACOSX_VERSION VERSION_LESS "10.9")
		# figure out what to do with Mavericks (10.9) later
	#	add_definitions("-D_DARWIN_UNLIMITED_SELECT")
		# support leopard and above
		set(CMAKE_OSX_DEPLOYMENT_TARGET 10.6)
		foreach(FLAGS CMAKE_C_FLAGS CMAKE_CXX_FLAGS CMAKE_EXE_LINKER_FLAGS CMAKE_SHARED_LINKER_FLAGS CMAKE_MODULE_LINKER_FLAGS)
			set(${FLAGS} "${${FLAGS}} -stdlib=libstdc++ -mmacosx-version-min=${CMAKE_OSX_DEPLOYMENT_TARGET}")
	  endforeach()
	else()
		set(CMAKE_OSX_DEPLOYMENT_TARGET 10.7)
		foreach(FLAGS CMAKE_C_FLAGS CMAKE_CXX_FLAGS CMAKE_EXE_LINKER_FLAGS CMAKE_SHARED_LINKER_FLAGS CMAKE_MODULE_LINKER_FLAGS)
			set(${FLAGS} "${${FLAGS}} -stdlib=libc++ -mmacosx-version-min=${CMAKE_OSX_DEPLOYMENT_TARGET}")
	  endforeach()
	endif()
endif()

# if (APPLE AND MACOSX_VERSION VERSION_GREATER "10.9.99")
# 	set(CMAKE_OSX_DEPLOYMENT_TARGET 10.10) # ?
# 	foreach(FLAGS CMAKE_C_FLAGS CMAKE_CXX_FLAGS CMAKE_EXE_LINKER_FLAGS CMAKE_SHARED_LINKER_FLAGS CMAKE_MODULE_LINKER_FLAGS)
# 			set(${FLAGS} "${${FLAGS}} -mmacosx-version-min=${CMAKE_OSX_DEPLOYMENT_TARGET} -arch x86_64")
# 			# we get "Illegal Instruction: 4" errors without on yosemite?!
# 			# set(${FLAGS} "${${FLAGS}} -isysroot /Applications/Xcode.app/Contents/Developer/Platforms/MacOSX.platform/Developer/SDKs/MacOSX10.10.sdk")
#   endforeach()
# endif()

if (IOS)
	if (${CMAKE_GENERATOR} STREQUAL "Xcode")
	else()
		set(CMAKE_OSX_DEPLOYMENT_TARGET 4.3)
		foreach(FLAGS CMAKE_C_FLAGS CMAKE_CXX_FLAGS CMAKE_EXE_LINKER_FLAGS CMAKE_SHARED_LINKER_FLAGS CMAKE_MODULE_LINKER_FLAGS)
				set(${FLAGS} "${${FLAGS}} -miphoneos-version-min=${CMAKE_OSX_DEPLOYMENT_TARGET}")
	  endforeach()
	endif()
endif()

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
	add_definitions("-DUSCXML_EXPORT")
else()
	add_definitions("-DUSCXML_STATIC")
endif()

# file(GLOB 
# 	GURL_SOURCE ${PROJECT_SOURCE_DIR}/contrib/src/google-url/googleurl/src/*.cc
# 	GURL_SOURCE ${PROJECT_SOURCE_DIR}/contrib/src/google-url/googleurl/src/*.h)
# list(APPEND USCXML_FILES ${GURL_SOURCE})
# list(APPEND USCXML_FILES ${PROJECT_SOURCE_DIR}/contrib/src/google-url/base/string16.cc)


# library suffix order
if (IOS)
	LIST(APPEND CMAKE_FIND_LIBRARY_SUFFIXES ".dylib")
endif()
set(CMAKE_FIND_LIBRARY_SUFFIXES_SHARED ${CMAKE_FIND_LIBRARY_SUFFIXES})
set(CMAKE_FIND_LIBRARY_SUFFIXES_STATIC .lib .a ${CMAKE_FIND_LIBRARY_SUFFIXES})

if(BUILD_PREFER_STATIC_LIBRARIES)
    SET(CMAKE_FIND_LIBRARY_SUFFIXES ${CMAKE_FIND_LIBRARY_SUFFIXES_STATIC})
endif()
SET(CMAKE_FIND_LIBRARY_SUFFIXES_ORIG ${CMAKE_FIND_LIBRARY_SUFFIXES})

# where should libraries end up?
if (DIST_PREPARE)
	if (CMAKE_CROSSCOMPILING)
		string(TOLOWER ${CMAKE_CROSSCOMPILING_TARGET} CMAKE_CROSSCOMPILING_TARGET_LC)
		set(OUTPUT_DIR
			${PROJECT_SOURCE_DIR}/package/cross-compiled/${CMAKE_CROSSCOMPILING_TARGET_LC}-${CMAKE_SYSTEM_VERSION}/${CMAKE_SYSTEM_PROCESSOR})
	else()
		set(OUTPUT_DIR
			${PROJECT_SOURCE_DIR}/package/${USCXML_PLATFORM_ID}/${CMAKE_CXX_COMPILER_ID_LC})
	endif()
else()
	set(OUTPUT_DIR ${PROJECT_BINARY_DIR})
endif()

set( CMAKE_RUNTIME_OUTPUT_DIRECTORY "${OUTPUT_DIR}/bin" )
set( CMAKE_LIBRARY_OUTPUT_DIRECTORY "${OUTPUT_DIR}/lib" )
set( CMAKE_ARCHIVE_OUTPUT_DIRECTORY "${OUTPUT_DIR}/lib" )
# do not override configuration specific outputs
# foreach( OUTPUT_CONFIG ${CMAKE_CONFIGURATION_TYPES} )
#     string( TOUPPER ${OUTPUT_CONFIG} OUTPUT_CONFIG )
#     set( CMAKE_RUNTIME_OUTPUT_DIRECTORY_${OUTPUT_CONFIG} "${OUTPUT_DIR}/bin" )
#     set( CMAKE_LIBRARY_OUTPUT_DIRECTORY_${OUTPUT_CONFIG} "${OUTPUT_DIR}/lib" )
#     set( CMAKE_ARCHIVE_OUTPUT_DIRECTORY_${OUTPUT_CONFIG} "${OUTPUT_DIR}/lib" )
# endforeach()

OPTION(BUILD_AS_PLUGINS "Build invokers, ioprocessors and datamodels as plugins" OFF)

if (BUILD_AS_PLUGINS)
	add_definitions("-DBUILD_AS_PLUGINS")
	include_directories("src/uscxml/plugins")
#	list(APPEND USCXML_FILES "src/uscxml/plugins/Plugins.cpp")
endif()

# this is where the config.h ends up
include_directories(${CMAKE_CURRENT_BINARY_DIR})
include_directories(src)

############################################################
# Dependent libraries
############################################################

if (NOT WIN32)
	# libxml2
	set(CMAKE_FIND_FRAMEWORK "LAST")

	# message("CMAKE_FIND_LIBRARY_SUFFIXES: ${CMAKE_FIND_LIBRARY_SUFFIXES}")
	# message("CMAKE_SYSTEM_PREFIX_PATH: ${CMAKE_SYSTEM_PREFIX_PATH}")
	# message("CMAKE_PREFIX_PATH: ${CMAKE_PREFIX_PATH}")
	# message("CMAKE_SYSTEM_INCLUDE_PATH: ${CMAKE_SYSTEM_INCLUDE_PATH}")
	# message("CMAKE_SYSTEM_LIBRARY_PATH: ${CMAKE_SYSTEM_LIBRARY_PATH}")
	# message("CMAKE_SYSTEM_PROGRAM_PATH: ${CMAKE_SYSTEM_PROGRAM_PATH}")
	# message("CMAKE_FIND_ROOT_PATH: ${CMAKE_FIND_ROOT_PATH}")

	# MacOSX Mavericks moved libxml2 into SDK
	if (APPLE AND "${MACOSX_VERSION}" VERSION_LESS "10.9.0")
		set(PC_LIBXML_INCLUDEDIR "/usr/include/libxml2/")
	endif()

	find_package(LibXml2 REQUIRED)
	include_directories(${LIBXML2_INCLUDE_DIR})
	list (APPEND USCXML_CORE_LIBS ${LIBXML2_LIBRARIES})
	set(XML_LIBRARIES ${LIBXML2_LIBRARIES})
	list (APPEND USCXML_CORE_LIBS "dl")
	list (APPEND USCXML_CORE_LIBS "pthread")
	if (APPLE)
		find_library(CORELOCATION_LIBRARY CoreLocation)
		if (CORELOCATION_LIBRARY AND OFF)
			list (APPEND USCXML_OPT_LIBS ${CORELOCATION_LIBRARY}/CoreLocation)
			set(CORELOCATION_FOUND ON)
		endif()
	endif()
	if (IOS)
		find_library(COREFOUNDATION_LIBRARY CoreFoundation)
		list (APPEND USCXML_CORE_LIBS ${COREFOUNDATION_LIBRARY}/CoreFoundation)
		find_library(SECURITY_LIBRARY Security)
		list (APPEND USCXML_CORE_LIBS ${SECURITY_LIBRARY}/Security)
		list (APPEND USCXML_CORE_LIBS "z")
	elseif(APPLE)
		find_library(APP_SERVICES_LIBRARY ApplicationServices)
		find_library(COREFOUNDATION_LIBRARY CoreFoundation)
		find_library(FOUNDATION_LIBRARY Foundation)
		list (APPEND USCXML_CORE_LIBS ${APP_SERVICES_LIBRARY})
		list (APPEND USCXML_CORE_LIBS ${COREFOUNDATION_LIBRARY})
		list (APPEND USCXML_CORE_LIBS ${FOUNDATION_LIBRARY})
	endif()
elseif(WIN32)
	list (APPEND XML_LIBRARIES "Ws2_32")
	list (APPEND XML_LIBRARIES "Winmm")
	list (APPEND XML_LIBRARIES "Iphlpapi")
	list (APPEND XML_LIBRARIES "Netapi32")
	list (APPEND USCXML_CORE_LIBS ${XML_LIBRARIES})
endif()

# ICU
# find_package(ICU REQUIRED)
# include_directories(${ICU_INCLUDE_DIRS})
# list (APPEND USCXML_CORE_LIBS ${ICU_LIBRARIES})

# CURL
find_package(CURL REQUIRED)
include_directories(${CURL_INCLUDE_DIRS})
list (APPEND USCXML_CORE_LIBS ${CURL_LIBRARIES})
if (WIN32)
	add_definitions("-DCURL_STATICLIB")
endif()
include(CheckCXXSourceCompiles)

set(CMAKE_REQUIRED_INCLUDES ${CURL_INCLUDE_DIRS})
set(CMAKE_REQUIRED_LIBRARIES ${CURL_LIBRARIES})

check_cxx_source_compiles("
	#include <curl/curl.h>
	int main(){return CURLOPT_MAIL_RCPT; }
" CURL_HAS_SMTP)

set(CMAKE_REQUIRED_INCLUDES)
set(CMAKE_REQUIRED_LIBRARIES)

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
#set(EVENT_SSL_FOUND OFF) # deactivate for now

#################################################
# Optional libraries

OPTION(DISABLE_ALL "Ignore all optional libraries" OFF)
if (BUILD_MINIMAL)
	SET(DISABLE_ALL ON)
endif()

if (APPLE OR IOS)
	OPTION(DISABLE_AUDIOTOOLBOX "Ignore AudioToolbox" OFF)
	if (NOT DISABLE_AUDIOTOOLBOX AND NOT DISABLE_ALL)
		find_library(AUDIOTOOLBOX AudioToolbox REQUIRED)
		if (MACOSX_VERSION VERSION_GREATER "10.10.99")
			# header files were moved it seems
			list (APPEND USCXML_OPT_LIBS ${AUDIOTOOLBOX})
		else()
			list (APPEND USCXML_OPT_LIBS ${AUDIOTOOLBOX}/AudioToolbox)
		endif()
		set(AUDIOTOOLBOX_FOUND ON)
	else()
		set(AUDIOTOOLBOX_FOUND OFF)
	endif()
	find_library(FOUNDATION_LIBRARY Foundation)
	if (MACOSX_VERSION VERSION_GREATER "10.10.99")
		list (APPEND USCXML_OPT_LIBS ${FOUNDATION_LIBRARY})
	else()
		list (APPEND USCXML_OPT_LIBS ${FOUNDATION_LIBRARY}/Foundation)
	endif()
	
	if (IOS)
		find_library(WTF_LIBRARY WTF)
		find_library(ICU_LIBRARY icucore REQUIRED)
		list (APPEND USCXML_OPT_LIBS ${WTF_LIBRARY})
		list (APPEND USCXML_OPT_LIBS ${ICU_LIBRARY})
	endif()

endif()

OPTION(DISABLE_JSC "Ignore JavaScriptCore" OFF)
if (NOT DISABLE_JSC AND NOT DISABLE_ALL AND NOT ECMA_FOUND)
	find_package(JSC)
	if (JSC_FOUND)
		set(ECMA_FOUND ON)
		if (NOT APPLE)
			include_directories(${JSC_INCLUDE_DIR})
		endif()
		list (APPEND USCXML_OPT_LIBS ${JSC_LIBRARY})
	endif()
else()
	set(JSC_FOUND OFF)
endif()

OPTION(DISABLE_V8 "Ignore Google's v8" OFF)
if (NOT DISABLE_V8 AND NOT DISABLE_ALL AND NOT ECMA_FOUND)
	find_package(V8)
	if (V8_FOUND)
		set(ECMA_FOUND ON)
		include_directories(${V8_INCLUDE_DIR})
		list (APPEND USCXML_OPT_LIBS ${V8_LIBRARY})
	endif()
else()
	set(V8_FOUND OFF)
endif()

OPTION(DISABLE_SPIDERMONKEY "Ignore SpiderMonkey" ON)
if (NOT DISABLE_SPIDERMONKEY AND NOT DISABLE_ALL AND NOT ECMA_FOUND)
	find_package(SpiderMonkey)
	if (SPIDERMONKEY_FOUND)
		set(ECMA_FOUND ON)
		include_directories(${SPIDERMONKEY_INCLUDE_DIR})
		if (UNIX)
			add_definitions(-DXP_UNIX)
		endif()
		list (APPEND USCXML_OPT_LIBS ${SPIDERMONKEY_LIBRARY})
	endif()
else()
	set(SPIDERMONKEY_FOUND OFF)
endif()


OPTION(DISABLE_LUA "Ignore Lua" OFF)
if (NOT DISABLE_LUA AND NOT DISABLE_ALL)
	set(CMAKE_FIND_LIBRARY_SUFFIXES ${CMAKE_FIND_LIBRARY_SUFFIXES_SHARED})
	find_package(Lua)
	if (LUA_FOUND)
		include_directories (${LUA_INCLUDE_DIR})
		include_directories(${PROJECT_SOURCE_DIR}/contrib/src/LuaBridge)
		list (APPEND USCXML_OPT_LIBS ${LUA_LIBRARIES})
	endif()
	set(CMAKE_FIND_LIBRARY_SUFFIXES ${CMAKE_FIND_LIBRARY_SUFFIXES_ORIG})
else()
	set(LUA_FOUND OFF)
endif()

OPTION(DISABLE_SSL "Ignore OpenSSL" OFF)
if (NOT DISABLE_SSL AND NOT DISABLE_ALL)
	find_package(OpenSSL)
	if (OPENSSL_FOUND)
		set(OPENSSL_HAS_ELIPTIC_CURVES OFF)
		include_directories(${OPENSSL_INCLUDE_DIR})
		list (APPEND USCXML_OPT_LIBS ${OPENSSL_LIBRARIES})
		if (EXISTS ${OPENSSL_INCLUDE_DIR}/openssl/ec.h)
			set(OPENSSL_HAS_ELIPTIC_CURVES ON)
		endif()
	endif()
else()
	set(OPENSSL_FOUND OFF)
endif()

if (EVENT_SSL_FOUND AND OPENSSL_FOUND)
	list (APPEND USCXML_CORE_LIBS ${OPENSSL_LIBRARIES})
endif()


OPTION(DISABLE_SWI "Ignore SWI Prolog" OFF)
if (NOT DISABLE_SWI AND NOT DISABLE_ALL)
	set(CMAKE_FIND_LIBRARY_SUFFIXES ${CMAKE_FIND_LIBRARY_SUFFIXES_SHARED})
	find_package(SWI)
	if (SWI_FOUND)
		if (SWI_CPP_INCLUDE_DIR)
			include_directories(${SWI_CPP_INCLUDE_DIR})
		else()
			include_directories(${PROJECT_SOURCE_DIR}/contrib/src/swi-pl)
		endif()
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
	set(CMAKE_FIND_LIBRARY_SUFFIXES ${CMAKE_FIND_LIBRARY_SUFFIXES_ORIG})
else()
	set(SWI_FOUND OFF)
endif()

OPTION(DISABLE_SQLITE "Ignore Sqlite3" OFF)
if (NOT DISABLE_SQLITE AND NOT DISABLE_ALL)
	find_package(Sqlite3)
	if (SQLITE3_FOUND)
	endif()
else()
	set(SQLITE3_FOUND OFF)
endif()

OPTION(DISABLE_FFMPEG "Ignore FFMpeg" OFF)
if (NOT DISABLE_FFMPEG AND NOT DISABLE_ALL)
	set(CMAKE_FIND_LIBRARY_SUFFIXES ${CMAKE_FIND_LIBRARY_SUFFIXES_SHARED})
	find_package(FFMPEG)
	if (FFMPEG_FOUND)
		include_directories (${FFMPEG_INCLUDE_DIRS})
		list (APPEND USCXML_OPT_LIBS ${FFMPEG_LIBRARIES})
		# required with static ffmpeg builds
		# set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -Wl,-Bsymbolic")
	endif()
	set(CMAKE_FIND_LIBRARY_SUFFIXES ${CMAKE_FIND_LIBRARY_SUFFIXES_ORIG})
else()
	set(FFMPEG_FOUND OFF)
endif()

OPTION(DISABLE_ICAL "Ignore iCal" OFF)
if (NOT DISABLE_ICAL AND NOT DISABLE_ALL)
	set(CMAKE_FIND_LIBRARY_SUFFIXES ${CMAKE_FIND_LIBRARY_SUFFIXES_SHARED})
	find_package(LIBICAL)
	if (LIBICAL_FOUND)
		include_directories (${LIBICAL_INCLUDE_DIR})
		list (APPEND USCXML_OPT_LIBS ${LIBICAL_LIBRARIES})
	endif()
	set(CMAKE_FIND_LIBRARY_SUFFIXES ${CMAKE_FIND_LIBRARY_SUFFIXES_ORIG})

else()
	set(LIBICAL_FOUND OFF)
endif()

OPTION(DISABLE_WEBRTC "Ignore libjingle (WebRTC)" OFF)
if (NOT DISABLE_WEBRTC AND NOT DISABLE_ALL)
	set(CMAKE_FIND_LIBRARY_SUFFIXES ${CMAKE_FIND_LIBRARY_SUFFIXES_SHARED})
	if (NOT DEFINED ENV{LIBJINGLE_ROOT_DIR})
		set(ENV{LIBJINGLE_ROOT_DIR} "/Users/sradomski/Documents/TK/Code/webrtc-work/trunk")
	endif()
	find_package(LibJingle)
	if (LIBJINGLE_FOUND)
		include_directories (${LIBJINGLE_INCLUDE_DIRS})
		list (APPEND USCXML_OPT_LIBS ${LIBJINGLE_LIBRARIES})
	endif()
	set(CMAKE_FIND_LIBRARY_SUFFIXES ${CMAKE_FIND_LIBRARY_SUFFIXES_ORIG})
else()
	set(LIBJINGLE_FOUND OFF)
endif()

OPTION(DISABLE_EXPECT "Ignore TCL/Expect" OFF)
if (NOT DISABLE_EXPECT AND NOT DISABLE_ALL)
	find_package(Expect)
	find_package(TCL)
	if (EXPECT_FOUND AND TCL_FOUND)
		include_directories (${EXPECT_INCLUDE_DIR})
		include_directories (${TCL_INCLUDE_PATH})
		list (APPEND USCXML_OPT_LIBS ${EXPECT_LIBRARY})
		list (APPEND USCXML_OPT_LIBS ${TCL_LIBRARY})
	endif()
else()
	set(EXPECT_FOUND OFF)
	set(TCL_FOUND OFF)
endif()

OPTION(DISABLE_LIBPURPLE "Ignore libpurple (instant messaging)" OFF)
if (NOT DISABLE_LIBPURPLE AND NOT DISABLE_ALL)
	set(CMAKE_FIND_LIBRARY_SUFFIXES ${CMAKE_FIND_LIBRARY_SUFFIXES_SHARED})
	find_package(LibPurple)
	if (LIBPURPLE_FOUND)
		find_package(ICONV)
		find_package(GLIB2)
		find_package(GObject)
		if (GLIB2_FOUND AND ICONV_FOUND AND GOBJECT_FOUND)
			include_directories (${LIBPURPLE_INCLUDE_DIR})
			list (APPEND USCXML_OPT_LIBS ${LIBPURPLE_LIBRARY})
			include_directories (${GLIB2_INCLUDE_DIRS})
			list (APPEND USCXML_OPT_LIBS ${GLIB2_LIBRARIES})
			include_directories (${ICONV_INCLUDE_DIR})
			list (APPEND USCXML_OPT_LIBS ${ICONV_LIBRARIES})
			include_directories (${GOBJECT_INCLUDE_DIR})
			list (APPEND USCXML_OPT_LIBS ${GOBJECT_LIBRARIES})
		else()
			set(LIBPURPLE_FOUND OFF)
		endif()	
	endif()
	set(CMAKE_FIND_LIBRARY_SUFFIXES ${CMAKE_FIND_LIBRARY_SUFFIXES_ORIG})
else()
	set(LIBPURPLE_FOUND OFF)
endif()

OPTION(DISABLE_UMUNDO "Ignore uMundo" OFF)
if (NOT DISABLE_UMUNDO AND NOT DISABLE_ALL)
	if (WIN32)
		find_package(UMUNDO COMPONENTS convenience)
	else()
		find_package(UMUNDO COMPONENTS rpc serial core)
		# find_package(UMUNDO COMPONENTS convenience)
	endif()
	if (UMUNDO_FOUND)
		include_directories (${UMUNDO_INCLUDE_DIR})
		list (APPEND USCXML_OPT_LIBS ${UMUNDO_LIBRARIES})
	#	add_definitions("-DUMUNDO_STATIC")
	endif()
else()
	set(UMUNDO_FOUND OFF)
endif()

OPTION(DISABLE_OSG "Ignore OpenSceneGraph" OFF)
if (NOT DISABLE_OSG AND NOT DISABLE_ALL)
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
	set(CMAKE_FIND_LIBRARY_SUFFIXES ${CMAKE_FIND_LIBRARY_SUFFIXES_ORIG})
else()
	set(OPENSCENEGRAPH_FOUND OFF)
	set(OPENGL_FOUND OFF)
endif()

OPTION(DISABLE_OPENAL "Ignore OpenAL" OFF)
if (NOT DISABLE_OPENAL AND NOT DISABLE_ALL)
	set(CMAKE_FIND_FRAMEWORK "FIRST")
	find_package(OpenAL)
	if (OPENAL_FOUND)
		list (APPEND USCXML_INCLUDE_DIRS ${OPENAL_INCLUDE_DIR})
		if (APPLE OR IOS)
			if (MACOSX_VERSION VERSION_GREATER "10.10.99")
				list (APPEND USCXML_OPT_LIBS ${OPENAL_LIBRARY})
			else()
				list (APPEND USCXML_OPT_LIBS ${OPENAL_LIBRARY}/OpenAL)
			endif()
		else()
			list (APPEND USCXML_OPT_LIBS ${OPENAL_LIBRARY})
		endif()
	else()
		find_package(OpenALKCAT)
		if (OPENAL_FOUND)
			list (APPEND USCXML_INCLUDE_DIRS ${OPENAL_INCLUDE_DIR})
			list (APPEND USCXML_OPT_LIBS ${OPENAL_LIBRARY})
		endif()
	endif()
	set(CMAKE_FIND_FRAMEWORK "LAST")
else()
	set(OPENAL_FOUND OFF)
endif()

if (NOT AUDIOTOOLBOX_FOUND)
	OPTION(DISABLE_LIBSNDFILE "Ignore libsndfile" OFF)
	if (NOT DISABLE_LIBSNDFILE AND NOT DISABLE_ALL)
		set(CMAKE_FIND_LIBRARY_SUFFIXES ${CMAKE_FIND_LIBRARY_SUFFIXES_SHARED})
		find_package(LIBSNDFILE)
		if (LIBSNDFILE_FOUND)
			list (APPEND USCXML_INCLUDE_DIRS ${LIBSNDFILE_INCLUDE_DIR})
			list (APPEND USCXML_OPT_LIBS ${LIBSNDFILE_LIBRARY})
		endif()
		set(CMAKE_FIND_LIBRARY_SUFFIXES ${CMAKE_FIND_LIBRARY_SUFFIXES_ORIG})
	else()
		set(LIBSNDFILE_FOUND OFF)
	endif()
endif()

OPTION(DISABLE_MILES "Ignore miles" OFF)
if (NOT DISABLE_MILES AND NOT DISABLE_ALL)
	set(CMAKE_FIND_LIBRARY_SUFFIXES ${CMAKE_FIND_LIBRARY_SUFFIXES_SHARED})
	find_package(MILES)
	#set(JPEG_ROOT_PATH "" CACHE STRING "Where to find libjpeg")
	if (MILES_FOUND)
		if (NOT WIN32)
			# openal is only needed for miles
			find_package(OpenAL)
			find_package(JPEG)
			find_package(ICONV)
	
			if (OPENAL_FOUND AND ICONV_FOUND AND JPEG_FOUND)
				include_directories (${MILES_INCLUDE_DIR})
				list (APPEND USCXML_OPT_LIBS ${MILES_LIBRARIES})
				include_directories (${ICONV_INCLUDE_DIR})
				list (APPEND USCXML_OPT_LIBS ${ICONV_LIBRARIES})
				include_directories (${JPEG_INCLUDE_DIR})
				list (APPEND USCXML_OPT_LIBS ${JPEG_LIBRARIES})
				include_directories (${OPENAL_INCLUDE_DIR})
				list (APPEND USCXML_OPT_LIBS ${OPENAL_LIBRARY})
			else()
				set(MILES_FOUND OFF)
			endif()
		else()
			include_directories (${MILES_INCLUDE_DIR})
			list (APPEND USCXML_OPT_LIBS ${MILES_LIBRARIES})
		endif()
	endif()
	set(CMAKE_FIND_LIBRARY_SUFFIXES ${CMAKE_FIND_LIBRARY_SUFFIXES_ORIG})
else()
	set(MILES_FOUND OFF)
endif()

OPTION(DISABLE_PROTOBUF "Ignore protobuf" OFF)
if (NOT DISABLE_PROTOBUF AND NOT DISABLE_ALL)
	set(CMAKE_FIND_LIBRARY_SUFFIXES ${CMAKE_FIND_LIBRARY_SUFFIXES_SHARED})
	find_package(Protobuf)
	if (PROTOBUF_FOUND)
		include_directories(${PROTOBUF_INCLUDE_DIRS})
		LIST(APPEND USCXML_OPT_LIBS optimized ${PROTOBUF_LIBRARY})
		LIST(APPEND USCXML_OPT_LIBS debug ${PROTOBUF_LIBRARY_DEBUG})
	endif()
	set(CMAKE_FIND_LIBRARY_SUFFIXES ${CMAKE_FIND_LIBRARY_SUFFIXES_ORIG})
else()
	set(PROTOBUF_FOUND OFF)
endif()

#################################################
# Gather source files
#################################################

# we use include instead of add_subdirectory because
# source groups do not work otherwise.

SET(USCXML_INVOKERS)
SET(USCXML_IOPROCESSORS)
SET(USCXML_ELEMENTS)
SET(USCXML_DATAMODELS)
SET(USCXML_LANGUAGE_BINDINGS)

include_directories(${USCXML_INCLUDE_DIRS})
add_subdirectory(src/uscxml)
if (WIN32)
	list(APPEND USCXML_FILES "${PROJECT_SOURCE_DIR}/contrib/src/getopt/getopt.c")
#	SET_SOURCE_FILES_PROPERTIES( ${PROJECT_SOURCE_DIR}/contrib/src/getopt/getopt.c PROPERTIES LANGUAGE CXX )
endif()

if (UNIX AND NOT APPLE)
	list (APPEND USCXML_CORE_LIBS "rt")
endif()

############################################################
# Binaries and tests
############################################################

set(ALL_SOURCE_FILES ${USCXML_FILES} ${USCXML_TRANSFORM_FILES})
list(SORT USCXML_FILES)
list(SORT USCXML_TRANSFORM_FILES)
# we cannot define source groups in sub directories!
foreach( FILE ${ALL_SOURCE_FILES} )
	get_filename_component(PATH ${FILE} PATH)
	get_filename_component(NAME ${FILE} NAME)

	# if (${NAME} MATCHES "Factory.cpp")
	# 	set_property(SOURCE ${FILE} PROPERTY COMPILE_FLAGS -std=c++11)
	# endif()
	# if (${PATH} MATCHES ".*datamodel\\/ecmascript\\/v8\\/*")
	# 	set_property(SOURCE ${FILE} PROPERTY COMPILE_FLAGS -std=c++11)
	# 	# message(${FILE})
	# endif()

	if (${PATH} MATCHES ".*datamodel\\/ecmascript.*")
		STRING(REGEX MATCH "[^\\/]*$" COMP_NAME ${PATH})
		if (COMP_NAME STREQUAL "ecmascript")
			source_group("Datamodel\\EcmaScript" FILES ${FILE})
		else()
			source_group("Datamodel\\EcmaScript\\${COMP_NAME}" FILES ${FILE})
		endif()
	elseif (${PATH} MATCHES ".*datamodel\\/prolog.*")
		STRING(REGEX MATCH "[^\\/]*$" COMP_NAME ${PATH})
		source_group("Datamodel\\Prolog\\${COMP_NAME}" FILES ${FILE})
	elseif (${PATH} MATCHES ".*datamodel\\/promela.*")
		source_group("Datamodel\\Promela" FILES ${FILE})
	elseif (${PATH} MATCHES ".*datamodel\\/xpath.*")
		source_group("Datamodel\\XPath" FILES ${FILE})
	elseif (${PATH} MATCHES ".*datamodel\\/lua.*")
		source_group("Datamodel\\Lua" FILES ${FILE})
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

	# elseif (${PATH} MATCHES ".*\\/google-url\\/.*")
	# 	STRING(REGEX MATCH "[^\\/]*$" COMP_NAME ${PATH})
	# 	source_group("Interpreter\\URL" FILES ${FILE})

	elseif (${FILE} MATCHES ".*\\/debug\\/.*")
		source_group("Interpreter\\debug" FILES ${FILE})
	elseif (${FILE} MATCHES ".*\\/plugins\\/.*")
		source_group("Interpreter\\plugins" FILES ${FILE})
	elseif (${FILE} MATCHES ".*\\/transform\\/.*")
		# source_group("Interpreter\\transform" FILES ${FILE})
	elseif (${FILE} MATCHES ".*\\/util\\/.*")
		source_group("Interpreter\\util" FILES ${FILE})
	elseif (${FILE} MATCHES ".*\\/concurrency\\/.*")
		source_group("Interpreter\\concurrency" FILES ${FILE})
	elseif (${FILE} MATCHES ".*\\/server\\/.*")
		source_group("Interpreter\\server" FILES ${FILE})
	elseif (${FILE} MATCHES ".*\\/messages\\/.*")
		source_group("Interpreter\\messages" FILES ${FILE})

	else ()
		source_group(Interpreter FILES ${FILE})
	endif()
endforeach()

# if (V8_FOUND AND BUILD_DM_ECMA)
# 	set_property(SOURCE ${ALL_SOURCE_FILES} PROPERTY COMPILE_FLAGS -Wno-c++11-extensions)
# endif()

# add compile time reducer
# see https://github.com/sakra/cotire
if (ENABLE_COTIRE)
	include(cotire)
endif()

#
# We cannot do this in subdirs?!
#

if (NOT BUILD_MINIMAL)
	# include html template in source file
	find_program(XXD_BINARY xxd)
	if (XXD_BINARY)
		add_custom_command(
			OUTPUT  ${CMAKE_SOURCE_DIR}/src/uscxml/plugins/invoker/xhtml/template/xhtml-invoker.inc.h
			COMMAND ${XXD_BINARY} -i template/xhtml-invoker.html template/xhtml-invoker.inc.h
		  DEPENDS ${CMAKE_SOURCE_DIR}/src/uscxml/plugins/invoker/xhtml/template/xhtml-invoker.html
			WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}/src/uscxml/plugins/invoker/xhtml
			COMMENT "Running xxd on uscxml/plugins/invoker/xhtml/template/xhtml-invoker.html"
		)
		LIST(APPEND USCXML_FILES ${CMAKE_SOURCE_DIR}/src/uscxml/plugins/invoker/xhtml/template/xhtml-invoker.inc.h)
	endif()
endif()

# build library
if (BUILD_AS_PLUGINS)
	add_library(uscxml ${USCXML_FILES})
	target_link_libraries(uscxml ${USCXML_CORE_LIBS})
	set_target_properties(uscxml PROPERTIES COMPILE_FLAGS "-DUSCXML_EXPORT")
#	set_target_properties(uscxml PROPERTIES COMPILE_FLAGS "-DPLUMA_EXPORTS")
	add_definitions(-DPLUMA_EXPORTS)
else()	
	add_library(uscxml ${USCXML_FILES})
	target_link_libraries(uscxml ${USCXML_OPT_LIBS} ${USCXML_CORE_LIBS})
endif()
INSTALL_LIBRARY(TARGETS uscxml COMPONENT library)

add_library(uscxml_transform ${USCXML_TRANSFORM_FILES})
target_link_libraries(uscxml_transform uscxml)
set_target_properties(uscxml_transform PROPERTIES PROJECT_LABEL "transform" FOLDER "uscxml")

INSTALL_LIBRARY(TARGETS uscxml_transform COMPONENT library)

if (NOT CMAKE_CROSSCOMPILING)
	if (ENABLE_COTIRE)
		set_target_properties(uscxml PROPERTIES COTIRE_CXX_PREFIX_HEADER_INIT "src/uscxml/pch.h")
		set_target_properties(uscxml PROPERTIES COTIRE_ADD_UNITY_BUILD FALSE)
		cotire(uscxml)
	endif()
endif()

if (NOT CMAKE_CROSSCOMPILING)
	if (WIN32)
		add_executable(uscxml-browser apps/uscxml-browser.cpp ${PROJECT_SOURCE_DIR}/contrib/src/getopt/getopt.c)
	else()
		add_executable(uscxml-browser apps/uscxml-browser.cpp)
	endif()
	target_link_libraries(uscxml-browser uscxml)
	
	
	if (NOT CMAKE_CROSSCOMPILING)
		if (ENABLE_COTIRE)
			set_target_properties(uscxml-browser PROPERTIES COTIRE_ADD_UNITY_BUILD FALSE)
		endif()
#		cotire(uscxml-browser)
	endif()
	set_target_properties(uscxml-browser PROPERTIES FOLDER "Apps")
	install_executable(TARGETS uscxml-browser COMPONENT tools)

	if (NOT BUILD_MINIMAL)
		if (WIN32)
			add_executable(uscxml-transform apps/uscxml-transform.cpp ${PROJECT_SOURCE_DIR}/contrib/src/getopt/getopt.c)
		else()
			add_executable(uscxml-transform apps/uscxml-transform.cpp)
		endif()
		target_link_libraries(uscxml-transform uscxml uscxml_transform)
		if (NOT CMAKE_CROSSCOMPILING)
			if (ENABLE_COTIRE)
				set_target_properties(uscxml-transform PROPERTIES COTIRE_ADD_UNITY_BUILD FALSE)
			endif()
		endif()
		set_target_properties(uscxml-transform PROPERTIES FOLDER "Apps")
		install_executable(TARGETS uscxml-transform COMPONENT tools)

		if (WIN32)
			add_executable(uscxml-analyze apps/uscxml-analyze.cpp ${PROJECT_SOURCE_DIR}/contrib/src/getopt/getopt.c)
		else()
			add_executable(uscxml-analyze apps/uscxml-analyze.cpp)
		endif()
		target_link_libraries(uscxml-analyze uscxml uscxml_transform)
		if (NOT CMAKE_CROSSCOMPILING)
			if (ENABLE_COTIRE)
				set_target_properties(uscxml-analyze PROPERTIES COTIRE_ADD_UNITY_BUILD FALSE)
			endif()
		endif()
		set_target_properties(uscxml-analyze PROPERTIES FOLDER "Apps")
		install_executable(TARGETS uscxml-analyze COMPONENT tools)

		if (WIN32)
			add_executable(uscxml-dot apps/uscxml-dot.cpp ${PROJECT_SOURCE_DIR}/contrib/src/getopt/getopt.c)
		else()
			add_executable(uscxml-dot apps/uscxml-dot.cpp)
		endif()
		target_link_libraries(uscxml-dot uscxml)
		if (NOT CMAKE_CROSSCOMPILING)
			if (ENABLE_COTIRE)
				set_target_properties(uscxml-dot PROPERTIES COTIRE_ADD_UNITY_BUILD FALSE)
			endif()
		endif()
		set_target_properties(uscxml-dot PROPERTIES FOLDER "Apps")
		install_executable(TARGETS uscxml-dot COMPONENT tools)
	endif()

	if (PROTOBUF_FOUND AND OFF)
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
	
	add_subdirectory(src/bindings)
endif()


############################################################
# Header Files
############################################################

file(GLOB_RECURSE USCXML_HEADERS 
  ${PROJECT_SOURCE_DIR}/src/*.h 
  ${PROJECT_SOURCE_DIR}/src/*.hpp 
  ${CMAKE_BINARY_DIR}/*.h)
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

if(CMAKE_BUILD_TYPE STREQUAL "Release")
	set(CMAKE_BUILD_TYPE_RELEASE ON)
elseif(CMAKE_BUILD_TYPE STREQUAL "Debug")
	set(CMAKE_BUILD_TYPE_DEBUG ON)
endif()



# enable config.h style compile time options and add as "uscxml/config.h"
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/config.h.in ${CMAKE_CURRENT_BINARY_DIR}/uscxml/config.h)
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/test/ctest/CTestCustom.ctest.in ${CMAKE_CURRENT_BINARY_DIR}/CTestCustom.ctest)

############################################################
# Some concluding remarks
############################################################

message(STATUS "Linking against external (check if you need to export in LD_LIBRARY_PATH or PATH):")
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
	elseif (LIBRARY MATCHES ".*\\.framework.*")
	elseif (LIBRARY MATCHES "mmi_proto.*")
	else()
		if (NOT SKIP_NEXT)
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

string(TOUPPER ${CMAKE_BUILD_TYPE} CMAKE_BUILD_TYPE_UC)
message(STATUS "  CXX Flags : " ${CMAKE_CXX_FLAGS} " " ${CMAKE_CXX_FLAGS_${CMAKE_BUILD_TYPE_UC}})
message(STATUS "  C   Flags : " ${CMAKE_C_FLAGS} " " ${CMAKE_C_FLAGS_${CMAKE_BUILD_TYPE_UC}})

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

cmake_policy(POP)

# This must always be last!
include(CPack)
