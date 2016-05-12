if (NOT APPLE)
	FIND_PATH(JSC_INCLUDE_DIR JavaScriptCore/JSBase.h
	  PATH_SUFFIXES webkitgtk-4.0 webkitgtk-3.0 webkitgtk-1.0
	  PATHS
	  /usr/local
	  /usr
	  /sw # Fink
	  /opt/local # DarwinPorts
	  /opt/csw # Blastwave
	  /opt
	)
endif()

FIND_PATH(HAS_JSC_JAVASCRIPTCORE_H JavaScriptCore/JavaScriptCore.h PATHS ${JSC_INCLUDE_DIR})
FIND_PATH(HAS_JSC_JAVASCRIPT_H JavaScriptCore/JavaScript.h PATHS ${JSC_INCLUDE_DIR})

FIND_LIBRARY(JSC_LIBRARY
  NAMES JavaScriptCore javascriptcoregtk-4.0 javascriptcoregtk-3.0 javascriptcoregtk-1.0
)

INCLUDE(FindPackageHandleStandardArgs)
if (NOT APPLE)
	FIND_PACKAGE_HANDLE_STANDARD_ARGS(JSC DEFAULT_MSG JSC_INCLUDE_DIR JSC_LIBRARY)
	MARK_AS_ADVANCED(JSC_LIBRARY JSC_INCLUDE_DIR)
else()
	FIND_PACKAGE_HANDLE_STANDARD_ARGS(JSC DEFAULT_MSG JSC_LIBRARY)
	MARK_AS_ADVANCED(JSC_LIBRARY)
endif()