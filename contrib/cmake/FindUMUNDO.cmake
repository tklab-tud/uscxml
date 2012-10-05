# - Find UMUNDO
# This module checks if UMundo is installed and determines where the
# include files and libraries are. This code sets the following
# variables:
#
# UMUNDO_INCLUDE_DIR             = The full path to the umundo headers
# UMUNDO_LIBRARIES               = All umundo libraries for release and debug builds
#
# Example:
#   find_package(UMUNDO REQUIRED util serial rpc)
#   include_directories(${UMUNDO_INCLUDE_DIR})
#

# is this a 64Bit host?
if(CMAKE_SIZEOF_VOID_P EQUAL 8)
	set(64BIT_LIB_POSTFIX 64)
else()
	set(64BIT_LIB_POSTFIX "")
endif()

###################################################
# where to search for umundo headers and libraries
###################################################
set(_UMUNDO_LIB_SEARCHPATH 
	"/usr/local" 
	"/opt/local" 
	"C:/Program Files (x86)/uMundo"
)

###################################################
# get a list of components the user requested
###################################################
set(_UMUNDO_COMPONENTS_TO_PROCESS)
foreach(_UMUNDO_COMPONENT ${UMUNDO_FIND_COMPONENTS})
	STRING(TOUPPER ${_UMUNDO_COMPONENT} _UMUNDO_COMPONENT_UC)
	list(APPEND _UMUNDO_COMPONENTS_TO_PROCESS ${_UMUNDO_COMPONENT_UC})
endforeach()
list(APPEND _UMUNDO_COMPONENTS_TO_PROCESS "CORE")
list(REMOVE_DUPLICATES _UMUNDO_COMPONENTS_TO_PROCESS)

###################################################
# find the umundo header files
###################################################
FIND_PATH(UMUNDO_INCLUDE_DIR umundo/core.h
  PATH_SUFFIXES include 
	PATHS ${_UMUNDO_LIB_SEARCHPATH}
	ENV UMUNDO_INCLUDE_DIR
)

###################################################
# iterate components and try to find libraries
# in debug and release configuration. For release
# we prefer MinSizeRel, for debug we prefer 
# RelWithDebInfo.
###################################################
SET(UMUNDO_LIBRARIES)
foreach (_UMUNDO_COMPONENT ${_UMUNDO_COMPONENTS_TO_PROCESS})
	SET(_CURR_COMPONENT "UMUNDO_${_UMUNDO_COMPONENT}_LIBRARY")
	STRING(TOLOWER ${_UMUNDO_COMPONENT}${64BIT_LIB_POSTFIX} _UMUNDO_COMPONENT_LC)

	# prefer MinSizeRel libraries
	FIND_LIBRARY(${_CURR_COMPONENT} 
		PATH_SUFFIXES lib
  	NAMES umundo${_UMUNDO_COMPONENT_LC}_s 
		PATHS ${_UMUNDO_LIB_SEARCHPATH}
		ENV UMUNDO_LIB_DIR
	)
	if (${_CURR_COMPONENT})
		list(APPEND UMUNDO_LIBRARIES optimized ${${_CURR_COMPONENT}})
	else()
		# if no minsize libraries were found try normal release
		FIND_LIBRARY(${_CURR_COMPONENT} 
			PATH_SUFFIXES lib
	  	NAMES umundo${_UMUNDO_COMPONENT_LC} 
			PATHS ${_UMUNDO_LIB_SEARCHPATH}
			ENV UMUNDO_LIB_DIR
		)
		if (${_CURR_COMPONENT})
			list(APPEND UMUNDO_LIBRARIES optimized ${${_CURR_COMPONENT}})
		endif()
	endif()
	
	# prefer RelWithDebInfo libraries
	FIND_LIBRARY(${_CURR_COMPONENT}_DEBUG 
		PATH_SUFFIXES lib
  	NAMES umundo${_UMUNDO_COMPONENT_LC}_rd
 		PATHS ${_UMUNDO_LIB_SEARCHPATH}
		ENV UMUNDO_LIB_DIR
	)
	if (${_CURR_COMPONENT}_DEBUG)
		list(APPEND UMUNDO_LIBRARIES debug ${${_CURR_COMPONENT}_DEBUG})
	else()
		FIND_LIBRARY(${_CURR_COMPONENT}_DEBUG 
			PATH_SUFFIXES lib
  		NAMES umundo${_UMUNDO_COMPONENT_LC}_d
 			PATHS ${_UMUNDO_LIB_SEARCHPATH}
			ENV UMUNDO_LIB_DIR
		)
		if (${_CURR_COMPONENT}_DEBUG)
			list(APPEND UMUNDO_LIBRARIES debug ${${_CURR_COMPONENT}_DEBUG})
		endif()
	endif()
	
	if (NOT ${_CURR_COMPONENT} AND NOT ${_CURR_COMPONENT}_DEBUG)
		message(FATAL_ERROR "Could not find umundo component ${_UMUNDO_COMPONENT}")
	endif()
endforeach()


INCLUDE(FindPackageHandleStandardArgs)
FIND_PACKAGE_HANDLE_STANDARD_ARGS(UMUNDO DEFAULT_MSG UMUNDO_LIBRARIES UMUNDO_INCLUDE_DIR)
MARK_AS_ADVANCED(UMUNDO_INCLUDE_DIR UMUNDO_LIBRARIES)
