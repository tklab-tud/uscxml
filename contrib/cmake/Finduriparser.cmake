find_path(URIPARSER_INCLUDE_DIR NAMES uriparser/UriBase.h)
find_library(URIPARSER_LIBRARY NAMES uriparser)

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(URIPARSER DEFAULT_MSG URIPARSER_LIBRARY URIPARSER_INCLUDE_DIR)

if (URIPARSER_FOUND)
  set(URIPARSER_LIBRARIES ${URIPARSER_LIBRARY})
  set(URIPARSER_INCLUDE_DIRS ${URIPARSER_INCLUDE_DIR})
endif()
  
mark_as_advanced(URIPARSER_INCLUDE_DIR)
mark_as_advanced(URIPARSER_LIBRARY)
