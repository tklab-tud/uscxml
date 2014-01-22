include(CheckCXXSourceCompiles)

FIND_PATH(LIBPURPLE_INCLUDE_DIR purple.h
  PATH_SUFFIXES include/libpurple src/libpurple
  PATHS
  /usr/local
  /usr
  /sw # Fink
  /opt/local # DarwinPorts
  /opt/csw # Blastwave
  /opt
)

FIND_LIBRARY(LIBPURPLE_LIBRARY_RELEASE
  NAMES purple libpurple libpurple-static
)
if (LIBPURPLE_LIBRARY_RELEASE)
	list(APPEND LIBPURPLE_LIBRARY optimized ${LIBPURPLE_LIBRARY_RELEASE})
endif()

FIND_LIBRARY(LIBPURPLE_LIBRARY_DEBUG
  NAMES purple_d libpurple_d libpurple-static_d
)
if (LIBPURPLE_LIBRARY_DEBUG)
	list(APPEND LIBPURPLE_LIBRARY debug ${LIBPURPLE_LIBRARY_DEBUG})
else()
	if (UNIX)
		list(APPEND LIBPURPLE_LIBRARY debug ${LIBPURPLE_LIBRARY_RELEASE})
	endif()
endif()

# message("LIBPURPLE_LIBRARY: ${LIBPURPLE_LIBRARY}")
# message("LIBPURPLE_INCLUDE_DIR: ${LIBPURPLE_INCLUDE_DIR}")

INCLUDE(FindPackageHandleStandardArgs)
FIND_PACKAGE_HANDLE_STANDARD_ARGS(LIBPURPLE DEFAULT_MSG LIBPURPLE_LIBRARY LIBPURPLE_INCLUDE_DIR)

# we need to check the API of libpurple, but need a couple more libraries
find_package(ICONV)
find_package(GLIB2)
find_package(GObject)
if (LIBPURPLE_FOUND AND GLIB2_FOUND AND ICONV_FOUND AND GOBJECT_FOUND)
	set(CMAKE_REQUIRED_INCLUDES ${LIBPURPLE_INCLUDE_DIR} ${GLIB2_INCLUDE_DIRS} ${ICONV_INCLUDE_DIR} ${GOBJECT_INCLUDE_DIR})
	set(CMAKE_REQUIRED_LIBRARIES ${LIBPURPLE_LIBRARY} ${GLIB2_LIBRARIES} ${ICONV_LIBRARIES} ${GOBJECT_LIBRARIES})
	if (LIBPURPLE_FOUND)
	  check_cxx_source_compiles("
		extern \"C\" {
			#include <purple.h>
		}
	  int main(){
			/* 
			 * There was a refactoring to glib datastructures, 
			 * The PurpleRequestFeature occured at the same time.
			 */
			PurpleRequestFeature _features;
	  }
	" LIBPURPLE_GLIB_DATASTRUCTS)
	endif()
	set(CMAKE_REQUIRED_INCLUDES)
	set(CMAKE_REQUIRED_LIBRARIES)
endif()

MARK_AS_ADVANCED(LIBPURPLE_LIBRARY LIBPURPLE_INCLUDE_DIR)
