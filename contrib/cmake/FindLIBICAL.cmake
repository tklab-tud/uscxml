# we cannot search for ical.h as we might find the wrong one without the libical suffix
FIND_PATH(LIBICAL_INCLUDE_DIR icalcomponent.h
  PATH_SUFFIXES include/libical
  PATHS
  /usr/local
  /usr
  /sw # Fink
  /opt/local # DarwinPorts
  /opt/csw # Blastwave
  /opt
)

FIND_LIBRARY(LIBICAL_LIBRARY_RELEASE
  NAMES ical libical libical-static
)
if (LIBICAL_LIBRARY_RELEASE)
	list(APPEND LIBICAL_LIBRARIES optimized ${LIBICAL_LIBRARY_RELEASE})
endif()

FIND_LIBRARY(LIBICAL_LIBRARY_DEBUG
  NAMES ical_d libical_d libical-static_d
)
if (LIBICAL_LIBRARY_DEBUG)
	list(APPEND LIBICAL_LIBRARIES debug ${LIBICAL_LIBRARY_DEBUG})
else()
	if (UNIX)
		list(APPEND LIBICAL_LIBRARIES debug ${LIBICAL_LIBRARY_RELEASE})
	endif()
endif()

FIND_LIBRARY(LIBICALSS_LIBRARY_RELEASE
  NAMES icalss libicalss libicalss-static
)
if (LIBICALSS_LIBRARY_RELEASE)
	list(APPEND LIBICAL_LIBRARIES optimized ${LIBICALSS_LIBRARY_RELEASE})
endif()

FIND_LIBRARY(LIBICALSS_LIBRARY_DEBUG
  NAMES icalss_d libicalss_d libicalss-static_d
)
if (LIBICALSS_LIBRARY_DEBUG)
	list(APPEND LIBICAL_LIBRARIES debug ${LIBICALSS_LIBRARY_DEBUG})
else()
	if (UNIX)
		list(APPEND LIBICAL_LIBRARIES debug ${LIBICALSS_LIBRARY_RELEASE})
	endif()
endif()


INCLUDE(FindPackageHandleStandardArgs)
FIND_PACKAGE_HANDLE_STANDARD_ARGS(LIBICAL DEFAULT_MSG LIBICAL_LIBRARIES LIBICAL_INCLUDE_DIR)
MARK_AS_ADVANCED(LIBICAL_LIBRARIES LIBICAL_INCLUDE_DIR)
