FIND_PATH(GMP_INCLUDE_DIR gmp.h
  PATH_SUFFIXES include
  PATHS
  /usr/local
  /usr
  /sw # Fink
  /opt/local # DarwinPorts
  /opt/csw # Blastwave
  /opt
  HINTS $ENV{GMP_SRC}
)

FIND_LIBRARY(GMP_LIBRARY_RELEASE
  NAMES gmp
  PATHS
  /usr/local
  /usr
  /sw # Fink
  /opt/local # DarwinPorts
  /opt/csw # Blastwave
  /opt
  HINTS $ENV{GMP_SRC}/.libs/
)
if (GMP_LIBRARY_RELEASE)
	list(APPEND GMP_LIBRARY optimized ${GMP_LIBRARY_RELEASE})
endif()

FIND_LIBRARY(GMP_LIBRARY_DEBUG
  NAMES GMP libGMP_static_d
  HINTS $ENV{GMP_SRC}/.libs/
)
if (GMP_LIBRARY_DEBUG)
	list(APPEND GMP_LIBRARY debug ${GMP_LIBRARY_DEBUG})
else()
	if (UNIX)
		list(APPEND GMP_LIBRARY debug ${GMP_LIBRARY_RELEASE})
	endif()
endif()

INCLUDE(FindPackageHandleStandardArgs)
FIND_PACKAGE_HANDLE_STANDARD_ARGS(GMP DEFAULT_MSG GMP_LIBRARY GMP_INCLUDE_DIR)
MARK_AS_ADVANCED(GMP_LIBRARY GMP_INCLUDE_DIR)
