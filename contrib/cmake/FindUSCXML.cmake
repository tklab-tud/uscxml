# - Find USCXML
# This module checks if uSCXML is installed and determines where the
# include files and libraries are. This code sets the following
# variables:
#
# USCXML_INCLUDE_DIR             = The full path to the uscxml headers
# USCXML_LIBRARIES               = All uscxml libraries for release and debug builds
#
# Example:
#   find_package(USCXML REQUIRED)
#   include_directories(${USCXML_INCLUDE_DIR})
#

###################################################
# where to search for uscxml headers and libraries
###################################################
set(_USCXML_LIB_SEARCHPATH
	${USCXML_LIBRARY_ROOT}
	"/usr/local"
	"/opt/local" 
	"C:/Program Files (x86)/uSCXML"
	"C:/Program Files/uSCXML"
)

###################################################
# find the uSCXML header files
###################################################
FIND_PATH(USCXML_INCLUDE_DIR uscxml/uscxml.h
  PATH_SUFFIXES include
	PATHS ${_USCXML_LIB_SEARCHPATH} ${USCXML_HEADER_ROOT}
	ENV USCXML_INCLUDE_DIR
)


set(USCXML_LIBRARIES)
# prefer MinSizeRel libraries
FIND_LIBRARY(USCXML_LIBRARY_RELEASE
	PATH_SUFFIXES lib
	NAMES uscxml_s 
	PATHS ${_USCXML_LIB_SEARCHPATH}
	ENV USCXML_LIB_DIR
)
if (USCXML_LIBRARY_RELEASE)
	list(APPEND USCXML_LIBRARIES optimized ${USCXML_LIBRARY_RELEASE})
else()
	# if no minsize libraries were found try normal release
	FIND_LIBRARY(USCXML_LIBRARY_RELEASE
		PATH_SUFFIXES lib
		NAMES uscxml
		PATHS ${_USCXML_LIB_SEARCHPATH}
		ENV USCXML_LIB_DIR
	)
	if (USCXML_LIBRARY_RELEASE)
		list(APPEND USCXML_LIBRARIES optimized USCXML_LIBRARY_RELEASE)
	endif()
endif()

# prefer release with debug libraries
FIND_LIBRARY(USCXML_LIBRARY_DEBUG
	PATH_SUFFIXES lib
	NAMES uscxml_rd
	PATHS ${_USCXML_LIB_SEARCHPATH}
	ENV USCXML_LIB_DIR
)
if ("${USCXML_LIBRARY_DEBUG}")
	list(APPEND USCXML_LIBRARIES debug ${USCXML_LIBRARY_DEBUG})
else()
	# go for normal debug libraries insteaf
	FIND_LIBRARY(USCXML_LIBRARY_DEBUG
		PATH_SUFFIXES lib
		NAMES uscxml_d
		PATHS ${_USCXML_LIB_SEARCHPATH}
		ENV USCXML_LIB_DIR
	)
	if ("${USCXML_LIBRARY_DEBUG}")
		list(APPEND USCXML_LIBRARIES debug USCXML_LIBRARY_DEBUG)
	endif()
endif()



INCLUDE(FindPackageHandleStandardArgs)
FIND_PACKAGE_HANDLE_STANDARD_ARGS(USCXML DEFAULT_MSG USCXML_LIBRARIES USCXML_INCLUDE_DIR)
MARK_AS_ADVANCED(USCXML_INCLUDE_DIR USCXML_LIBRARIES)
