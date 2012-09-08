FIND_PATH(ARABICA_INCLUDE_DIR Arabica/getparam.hpp
  PATH_SUFFIXES include/arabica include
  PATHS
  /usr/local
  /usr
  /sw # Fink
  /opt/local # DarwinPorts
  /opt/csw # Blastwave
  /opt
  HINTS $ENV{ARABICA_SRC}
)

FIND_LIBRARY(ARABICA_LIBRARY
  NAMES arabica
  HINTS $ENV{ARABICA_SRC}/src/.libs/

)

INCLUDE(FindPackageHandleStandardArgs)
FIND_PACKAGE_HANDLE_STANDARD_ARGS(Arabica DEFAULT_MSG ARABICA_LIBRARY ARABICA_INCLUDE_DIR)
MARK_AS_ADVANCED(ARABICA_LIBRARY ARABICA_INCLUDE_DIR)
