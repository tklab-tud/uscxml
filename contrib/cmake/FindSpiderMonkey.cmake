FIND_PATH(SPIDERMONKEY_INCLUDE_DIR jsapi.h
  PATH_SUFFIXES include/js
  PATHS
  /usr/local
  /usr
  /sw # Fink
  /opt/local # DarwinPorts
  /opt/csw # Blastwave
  /opt
)

FIND_LIBRARY(SPIDERMONKEY_LIBRARY NAMES js
  PATH_SUFFIXES lib
  PATHS
  /usr/local
  /usr
  /sw # Fink
  /opt/local # DarwinPorts
  /opt/csw # Blastwave
  /opt
)

INCLUDE(FindPackageHandleStandardArgs)
FIND_PACKAGE_HANDLE_STANDARD_ARGS(SPIDERMONKEY DEFAULT_MSG SPIDERMONKEY_LIBRARY SPIDERMONKEY_INCLUDE_DIR)
MARK_AS_ADVANCED(JSC_LIBRARY JSC_INCLUDE_DIR)
