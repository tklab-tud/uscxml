set(64BIT_HOST OFF)
if(CMAKE_SIZEOF_VOID_P EQUAL 8)
	set(64BIT_HOST ON)
endif()

set(SWI_PLATFORM_ID)
if (UNIX)
	if (APPLE AND 64BIT_HOST)
		set(SWI_PLATFORM_ID "x86_64-${CMAKE_SYSTEM_NAME}${CMAKE_SYSTEM_VERSION}")
	else()
		set(SWI_PLATFORM_ID "${CMAKE_SYSTEM_PROCESSOR}-${CMAKE_SYSTEM_NAME}${CMAKE_SYSTEM_VERSION}")
	endif()
else()
	set(SWI_PLATFORM_ID "${CMAKE_SYSTEM_PROCESSOR}-windows")
endif()

if (SWI_PLATFORM_ID)
	string(TOLOWER ${SWI_PLATFORM_ID} SWI_PLATFORM_ID)
endif()

#message("SWI_PLATFORM_ID: ${SWI_PLATFORM_ID}")

set (SWI_SEARCH_PATHS)
list (APPEND SWI_SEARCH_PATHS 
	$ENV{SWI_DIR}
	${CMAKE_FIND_ROOT_PATH}
	"/usr/lib/swi-prolog/"
	"/opt/local/"
	"C:/Program Files (x86)/swipl"
	"C:/Program Files/swipl"
)

#message("SWI_SEARCH_PATHS: ${SWI_SEARCH_PATHS}")

set (SWI_VERSION)
set (LOOP_DONE 0)
foreach(SWI_SEARCH_PATH ${SWI_SEARCH_PATHS})
	if(NOT LOOP_DONE)
		file(GLOB SWI_VERSIONS ${SWI_SEARCH_PATH}/lib/swipl*)
		if (SWI_VERSIONS)
			set(LOOP_DONE 1)
			list(SORT SWI_VERSIONS)
			list(REVERSE SWI_VERSIONS)
			list(GET SWI_VERSIONS 0 SWI_VERSION)
			STRING(REGEX REPLACE ".*(([0-9]+).([0-9]+).([0-9]+))$" "\\1" SWI_VERSION "${SWI_VERSION}")
		endif()
	endif()
endforeach()

# -- find prolog headers
FIND_PATH(SWI_INCLUDE_DIR SWI-Prolog.h
  PATH_SUFFIXES 
		include 
		lib/swipl-${SWI_VERSION}/include
  PATHS ${SWI_SEARCH_PATHS}
)

FIND_PATH(SWI_CPP_INCLUDE_DIR SWI-cpp.h
  PATH_SUFFIXES 
		packages/cpp 
		lib/swipl-${SWI_VERSION}/include
  PATHS ${SWI_SEARCH_PATHS}
)

FIND_PROGRAM(SWI_BINARY swipl
  PATH_SUFFIXES 
		src
		lib/swipl-${SWI_VERSION}/bin/${SWI_PLATFORM_ID}
  PATHS ${SWI_SEARCH_PATHS}
)

FIND_LIBRARY(SWI_LIBRARY_RELEASE
  NAMES libswipl swipl
  PATH_SUFFIXES
		lib/${SWI_PLATFORM_ID}                   # still in source directory
		lib/swipl-${SWI_VERSION}/lib/${SWI_PLATFORM_ID}   # after make install
	PATHS ${SWI_SEARCH_PATHS}
)

FIND_LIBRARY(SWI_LIBRARY_DEBUG
  NAMES libswipl_d swipl_d
  PATH_SUFFIXES
		lib/${SWI_PLATFORM_ID}                     # still in source directory
		lib/swipl-${SWI_VERSION}/lib/${SWI_PLATFORM_ID}     # after make install
	PATHS ${SWI_SEARCH_PATHS}
)

if (NOT SWI_LIBRARY_DEBUG)# no explicit debug build, just reuse release
	if (UNIX)
		set(SWI_LIBRARY_DEBUG ${SWI_LIBRARY_RELEASE})
	endif()
endif()

if (SWI_LIBRARY_RELEASE)
	list(APPEND SWI_LIBRARY optimized ${SWI_LIBRARY_RELEASE})
	if (SWI_LIBRARY_DEBUG)
		list(APPEND SWI_LIBRARY debug ${SWI_LIBRARY_DEBUG})
	elseif(UNIX)
		list(APPEND SWI_LIBRARY debug ${SWI_LIBRARY_RELEASE})
	else()
		message(FATAL_ERROR "Cannot find debug version of SWI")
	endif()
endif()

#message(FATAL_ERROR "SWI_BINARY: ${SWI_BINARY} / SWI_LIBRARY_RELEASE: ${SWI_LIBRARY_RELEASE} / SWI_LIBRARY_DEBUG: ${SWI_LIBRARY_DEBUG} / SWI_INCLUDE_DIR: ${SWI_INCLUDE_DIR} / SWI_CPP_INCLUDE_DIR: ${SWI_CPP_INCLUDE_DIR}")

INCLUDE(FindPackageHandleStandardArgs)
FIND_PACKAGE_HANDLE_STANDARD_ARGS(SWI DEFAULT_MSG SWI_LIBRARY SWI_BINARY SWI_INCLUDE_DIR SWI_CPP_INCLUDE_DIR)
MARK_AS_ADVANCED(SWI_LIBRARY SWI_INCLUDE_DIR)
