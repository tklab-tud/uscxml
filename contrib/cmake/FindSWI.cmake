set (SWI_SEARCH_PATHS)
list (APPEND SWI_SEARCH_PATHS 
	$ENV{SWI_HOME}
	${CMAKE_FIND_ROOT_PATH}
	"/usr/lib/swi-prolog/"
	"/opt/local/"
	"/usr/local/"
	"C:/Program Files (x86)/swipl"
	"C:/Program Files/swipl"
)


if (NOT WIN32)
	include(FindPkgConfig)
	pkg_check_modules(SWI swipl)
endif (NOT WIN32)

if (SWI_FOUND)
	# message("SWI_LIBRARIES: ${SWI_LIBRARIES}")
	# message("SWI_LIBRARY_DIRS: ${SWI_LIBRARY_DIRS}")
	# message("SWI_LDFLAGS: ${SWI_LDFLAGS}")
	# message("SWI_LDFLAGS_OTHER: ${SWI_LDFLAGS_OTHER}")
	# message("SWI_INCLUDE_DIRS: ${SWI_INCLUDE_DIRS}")
	# message("SWI_CFLAGS: ${SWI_CFLAGS}")
	# message("SWI_CFLAGS_OTHER: ${SWI_CFLAGS_OTHER}")
	# message("SWI_VERSION: ${SWI_VERSION}")
	# 
	# message("SWI_LIBRARIES_STATIC: ${SWI_LIBRARIES_STATIC}")
	# message("SWI_LIBRARY_DIRS_STATIC: ${SWI_LIBRARY_DIRS_STATIC}")
	# message("SWI_LDFLAGS_STATIC: ${SWI_LDFLAGS_STATIC}")
	# message("SWI_LDFLAGS_OTHER_STATIC: ${SWI_LDFLAGS_OTHER_STATIC}")
	# message("SWI_INCLUDE_DIRS_STATIC: ${SWI_INCLUDE_DIRS_STATIC}")
	# message("SWI_CFLAGS_STATIC: ${SWI_CFLAGS_STATIC}")
	# message("SWI_CFLAGS_OTHER_STATIC: ${SWI_CFLAGS_OTHER_STATIC}")
	# message(FATAL_ERROR "")

	if (SWI_INCLUDE_DIRS)
		set(SWI_INCLUDE_DIR ${SWI_INCLUDE_DIRS})
	else()
		FIND_PATH(SWI_INCLUDE_DIR SWI-Prolog.h
		  PATH_SUFFIXES 
				include
				lib/swipl-${SWI_VERSION}/include
		  PATHS ${SWI_SEARCH_PATHS}
		)
	endif()

	FIND_LIBRARY(SWI_LIBRARY
	  NAMES libswipl swipl
		PATHS ${SWI_LIBRARY_DIRS}
	)

	FIND_PROGRAM(SWI_BINARY swipl)
	
	FIND_PATH(SWI_CPP_INCLUDE_DIR SWI-cpp.h
	  PATHS 
		${SWI_INCLUDE_DIRS}
		${PROJECT_SOURCE_DIR}/contrib/src/swi-pl
	)

else()
	set(64BIT_HOST OFF)
	if(CMAKE_SIZEOF_VOID_P EQUAL 8)
		set(64BIT_HOST ON)
	endif()

	set(SWI_PLATFORM_ID)
	if (UNIX)
		if (APPLE AND 64BIT_HOST)
			set(SWI_PLATFORM_ID "x86_64-${CMAKE_SYSTEM_NAME}${CMAKE_SYSTEM_VERSION}")
		else()
			set(SWI_PLATFORM_ID "${CMAKE_SYSTEM_PROCESSOR}-${CMAKE_SYSTEM_NAME}")
		endif()
	else()
		set(SWI_PLATFORM_ID "${CMAKE_SYSTEM_PROCESSOR}-windows")
	endif()

	if (SWI_PLATFORM_ID)
		string(TOLOWER ${SWI_PLATFORM_ID} SWI_PLATFORM_ID)
	endif()

	#message("SWI_PLATFORM_ID: ${SWI_PLATFORM_ID}")

	list (APPEND SWI_SEARCH_PATHS 
		$ENV{SWI_HOME}
		${CMAKE_FIND_ROOT_PATH}
		"/usr/lib/swi-prolog/"
		"/opt/local/"
		"/usr/local/"
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
	#			message("SWI_VERSIONS: ${SWI_VERSIONS}")
				set(LOOP_DONE 1)
				list(SORT SWI_VERSIONS)
				list(REVERSE SWI_VERSIONS)
				list(GET SWI_VERSIONS 0 SWI_VERSION)
				STRING(REGEX REPLACE ".*(([0-9]+).([0-9]+).([0-9]+))$" "\\1" SWI_VERSION "${SWI_VERSION}")
			endif()
		endif()
	endforeach()

	#message("SWI_VERSION: ${SWI_VERSION}")

	set(SWI_PLATFORMS)
	foreach (SWI_SEARCH_PATH ${SWI_SEARCH_PATHS})
		file(GLOB CURR_SWI_PLATFORMS ${SWI_SEARCH_PATH}/lib/swipl-${SWI_VERSION}/lib/*)
		foreach(CURR_SWI_PLATFORM ${CURR_SWI_PLATFORMS})
	  	if(IS_DIRECTORY ${CURR_SWI_PLATFORM})
				list(APPEND SWI_PLATFORMS ${CURR_SWI_PLATFORM})
			endif()
		endforeach()
	endforeach()
	#message(FATAL_ERROR "SWI_PLATFORMS: ${SWI_PLATFORMS}")

	#message("SWI_VERSION: ${SWI_VERSION}")

	# -- find prolog headers
	FIND_PATH(SWI_INCLUDE_DIR SWI-Prolog.h
	  PATH_SUFFIXES 
			include
			lib/swipl-${SWI_VERSION}/include
	  PATHS ${SWI_SEARCH_PATHS}
	)

	#message("SWI_INCLUDE_DIR: ${SWI_INCLUDE_DIR}")

	FIND_PATH(SWI_CPP_INCLUDE_DIR SWI-cpp.h
	  PATH_SUFFIXES 
			packages/cpp 
			lib/swipl-${SWI_VERSION}/include
	  PATHS 
			${SWI_SEARCH_PATHS}
			${PROJECT_SOURCE_DIR}/contrib/src/swi-pl
	)

	#message("SWI_CPP_INCLUDE_DIR: ${SWI_CPP_INCLUDE_DIR}")

	FIND_PROGRAM(SWI_BINARY swipl
	  PATH_SUFFIXES 
			src
			lib/swipl-${SWI_VERSION}/bin/${SWI_PLATFORM_ID}
	  PATHS ${SWI_SEARCH_PATHS}
	)

	FIND_LIBRARY(SWI_LIBRARY_RELEASE
	  NAMES libswipl swipl
	  PATH_SUFFIXES
			lib/${SWI_PLATFORM_ID}                            # still in source directory
			lib/swipl-${SWI_VERSION}/lib/${SWI_PLATFORM_ID}   # after make install
		
		PATHS ${SWI_SEARCH_PATHS} ${SWI_PLATFORMS}
	)

	FIND_LIBRARY(SWI_LIBRARY_DEBUG
	  NAMES libswipl_d swipl_d
	  PATH_SUFFIXES
			lib/${SWI_PLATFORM_ID}                     # still in source directory
			lib/swipl-${SWI_VERSION}/lib/${SWI_PLATFORM_ID}     # after make install
		PATHS ${SWI_SEARCH_PATHS} ${SWI_PLATFORMS}
	)

	if (NOT SWI_LIBRARY_DEBUG) # no explicit debug build, just reuse release
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
endif()

#message(FATAL_ERROR "SWI_BINARY: ${SWI_BINARY} / SWI_LIBRARY_RELEASE: ${SWI_LIBRARY_RELEASE} / SWI_LIBRARY_DEBUG: ${SWI_LIBRARY_DEBUG} / SWI_INCLUDE_DIR: ${SWI_INCLUDE_DIR} / SWI_CPP_INCLUDE_DIR: ${SWI_CPP_INCLUDE_DIR}")

INCLUDE(FindPackageHandleStandardArgs)
FIND_PACKAGE_HANDLE_STANDARD_ARGS(SWI DEFAULT_MSG SWI_LIBRARY SWI_BINARY SWI_INCLUDE_DIR SWI_CPP_INCLUDE_DIR)


if (SWI_FOUND)
	include(CheckCXXSourceCompiles)
	
	set(CMAKE_REQUIRED_INCLUDES ${SWI_INCLUDE_DIR} ${SWI_CPP_INCLUDE_DIR})
	
	set(CMAKE_REQUIRED_LIBRARIES ${SWI_LIBRARY})

	# check for new reinterpret_cast<void (*)()>(f) for foreign functions with in SWI 7.x and above
	check_cxx_source_compiles("
		#include <SWI-cpp.h>
		int main(){
	  }
	" SWI_REINTERPRET_FOREIGN)

	check_cxx_source_compiles("
		#include <SWI-Prolog.h>
		int main(){
			int a = 0;
			switch(a) {
				case PL_NIL:
				break;
			}
	  }
	" SWI_HAS_PL_NIL)
	
	check_cxx_source_compiles("
		#include <SWI-Prolog.h>
		int main(){
			int a = 0;
			switch(a) {
				case PL_DICT:
				break;
			}
	  }
	" SWI_HAS_PL_DICT)
	
	check_cxx_source_compiles("
		#include <SWI-Prolog.h>
		int main(){
			int a = 0;
			switch(a) {
				case PL_LIST_PAIR:
				break;
			}
	  }
	" SWI_HAS_PL_LIST_PAIR)
	
	set(CMAKE_REQUIRED_INCLUDES)
	set(CMAKE_REQUIRED_LIBRARIES)
endif()

MARK_AS_ADVANCED(SWI_LIBRARY SWI_INCLUDE_DIR)


