FIND_PATH(EXPECT_INCLUDE_DIR expect.h
  PATH_SUFFIXES include
  PATHS
  /usr/local
  /usr
  /sw # Fink
  /opt/local # DarwinPorts
  /opt/csw # Blastwave
  /opt
)

set(EXPECT_LIBRARY)

FIND_LIBRARY(EXPECT_LIBRARY_RELEASE
  NAMES expect
  PATHS
  /usr/local
  /usr
  /sw
  /opt/local
  /opt/csw
  /opt
)
if (EXPECT_LIBRARY_RELEASE)
	list(APPEND EXPECT_LIBRARY optimized ${EXPECT_LIBRARY_RELEASE})
endif()

FIND_LIBRARY(EXPECT_LIBRARY_DEBUG
  NAMES expectd expect_d
  PATHS
  /usr/local
  /usr
  /sw
  /opt/local
  /opt/csw
  /opt
)
if (EXPECT_LIBRARY_DEBUG)
	list(APPEND EXPECT_LIBRARY debug ${EXPECT_LIBRARY_DEBUG})
else()
	list(APPEND EXPECT_LIBRARY debug ${EXPECT_LIBRARY_RELEASE})
endif()

# handle the QUIETLY and REQUIRED arguments and set OPENAL_FOUND to TRUE if
# all listed variables are TRUE
INCLUDE(FindPackageHandleStandardArgs)
FIND_PACKAGE_HANDLE_STANDARD_ARGS(EXPECT DEFAULT_MSG EXPECT_LIBRARY_RELEASE EXPECT_LIBRARY EXPECT_INCLUDE_DIR)
MARK_AS_ADVANCED(EXPECT_LIBRARY_RELEASE EXPECT_LIBRARY_DEBUG)
