# - Find Miles
# This module checks if Miles is installed and determines where the
# include files and libraries are. This code sets the following
# variables:
#
# MILES_INCLUDE_DIR             = The full path to the miles headers
# MILES_LIBRARIES               = All miles libraries for release and debug builds
#
# Example:
#   find_package(MILES REQUIRED audio network)
#   include_directories(${MILES_INCLUDE_DIR})
#

# is this a 64Bit host?
# if (NOT APPLE)
# 	if(CMAKE_SIZEOF_VOID_P EQUAL 8)
# 		set(_MILES_64BIT_LIB_POSTFIX 64)
# 	else()
# 		set(_MILES_64BIT_LIB_POSTFIX "")
# 	endif()
# endif()

###################################################
# where to search for miles headers and libraries
###################################################
set(_MILES_LIB_SEARCHPATH 
	"/usr/local" 
	"/opt/local" 
	"C:/Program Files (x86)/miles"
	"C:/Program Files/miles"
)

###################################################
# get a list of components the user requested
###################################################
set(_MILES_COMPONENTS_TO_PROCESS)
foreach(_MILES_COMPONENT ${MILES_FIND_COMPONENTS})
	STRING(TOUPPER ${_MILES_COMPONENT} _MILES_COMPONENT_UC)
	list(APPEND _MILES_COMPONENTS_TO_PROCESS ${_MILES_COMPONENT_UC})
endforeach()
list(APPEND _MILES_COMPONENTS_TO_PROCESS "CORE")
list(REMOVE_DUPLICATES _MILES_COMPONENTS_TO_PROCESS)

###################################################
# find the miles header files
###################################################
FIND_PATH(MILES_INCLUDE_DIR miles/miles.h
  PATH_SUFFIXES include 
	PATHS ${_MILES_LIB_SEARCHPATH}
	ENV MILES_INCLUDE_DIR
)

###################################################
# iterate components and try to find libraries
# in debug and release configuration. For release
# we prefer MinSizeRel, for debug we prefer 
# RelWithDebInfo.
###################################################
SET(MILES_LIBRARIES)

list(LENGTH MILES_FIND_COMPONENTS MILES_NR_COMPONENTS)
if (MILES_NR_COMPONENTS GREATER 0)
	foreach (_MILES_COMPONENT ${_MILES_COMPONENTS_TO_PROCESS})
		SET(_CURR_COMPONENT "MILES_${_MILES_COMPONENT}_LIBRARY")
		STRING(TOLOWER ${_MILES_COMPONENT}${_MILES_64BIT_LIB_POSTFIX} _MILES_COMPONENT_LC)

		# prefer MinSizeRel libraries
		FIND_LIBRARY(${_CURR_COMPONENT} 
			PATH_SUFFIXES lib
	  	NAMES miles_${_MILES_COMPONENT_LC}_s 
			PATHS ${_MILES_LIB_SEARCHPATH}
			ENV MILES_LIB_DIR
		)
		if (${_CURR_COMPONENT})
			list(APPEND MILES_LIBRARIES optimized ${${_CURR_COMPONENT}})
		else()
			# if no minsize libraries were found try normal release
			FIND_LIBRARY(${_CURR_COMPONENT} 
				PATH_SUFFIXES lib
		  	NAMES miles_${_MILES_COMPONENT_LC} 
				PATHS ${_MILES_LIB_SEARCHPATH}
				ENV MILES_LIB_DIR
			)
			if (${_CURR_COMPONENT})
				list(APPEND MILES_LIBRARIES optimized ${${_CURR_COMPONENT}})
			endif()
		endif()
	
		# prefer RelWithDebInfo libraries
		FIND_LIBRARY(${_CURR_COMPONENT}_DEBUG 
			PATH_SUFFIXES lib
	  	NAMES miles_${_MILES_COMPONENT_LC}_rd
	 		PATHS ${_MILES_LIB_SEARCHPATH}
			ENV MILES_LIB_DIR
		)
		if (${_CURR_COMPONENT}_DEBUG)
			list(APPEND MILES_LIBRARIES debug ${${_CURR_COMPONENT}_DEBUG})
		else()
			FIND_LIBRARY(${_CURR_COMPONENT}_DEBUG 
				PATH_SUFFIXES lib
	  		NAMES miles_${_MILES_COMPONENT_LC}_d
	 			PATHS ${_MILES_LIB_SEARCHPATH}
				ENV MILES_LIB_DIR
			)
			if (${_CURR_COMPONENT}_DEBUG)
				list(APPEND MILES_LIBRARIES debug ${${_CURR_COMPONENT}_DEBUG})
			endif()
		endif()	
	endforeach()
else()
	FIND_LIBRARY(MILES_RELEASE
		PATH_SUFFIXES lib
		NAMES miles_s 
		PATHS ${_MILES_LIB_SEARCHPATH}
		ENV MILES_LIB_DIR
	)
	if (MILES_RELEASE)
		list(APPEND MILES_LIBRARIES optimized ${MILES_RELEASE})
	else()
		# if no minsize libraries were found try normal release
		FIND_LIBRARY(MILES_RELEASE
			PATH_SUFFIXES lib
	  	NAMES miles
			PATHS ${_MILES_LIB_SEARCHPATH}
			ENV MILES_LIB_DIR
		)
		if (MILES_RELEASE)
			list(APPEND MILES_LIBRARIES optimized ${MILES_RELEASE})
		endif()
	endif()

	# prefer RelWithDebInfo libraries
	FIND_LIBRARY(MILES_DEBUG 
		PATH_SUFFIXES lib
  	NAMES miles_rd
 		PATHS ${_MILES_LIB_SEARCHPATH}
		ENV MILES_LIB_DIR
	)
	if (MILES_DEBUG)
		list(APPEND MILES_LIBRARIES debug ${MILES_DEBUG})
	else()
		FIND_LIBRARY(MILES_DEBUG 
			PATH_SUFFIXES lib
  		NAMES miles_d
 			PATHS ${_MILES_LIB_SEARCHPATH}
			ENV MILES_LIB_DIR
		)
		if (MILES_DEBUG)
			list(APPEND MILES_LIBRARIES debug ${MILES_DEBUG})
		endif()
	endif()	

endif()

INCLUDE(FindPackageHandleStandardArgs)
FIND_PACKAGE_HANDLE_STANDARD_ARGS(MILES DEFAULT_MSG MILES_LIBRARIES MILES_INCLUDE_DIR)
MARK_AS_ADVANCED(MILES_INCLUDE_DIR MILES_LIBRARIES)
