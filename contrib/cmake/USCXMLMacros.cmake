
##############################################################################
# Provide custom install_* macros to account for all files
##############################################################################

include(CMakeParseArguments)

function(INSTALL_HEADERS)
	set(options)
	set(oneValueArgs COMPONENT)
	set(multiValueArgs HEADERS)
	cmake_parse_arguments(INSTALL_HEADERS "${options}" "${oneValueArgs}" "${multiValueArgs}" ${ARGN})
	FOREACH(HEADER ${INSTALL_HEADERS_HEADERS})
#		message(STATUS "ADDING HEADER ${HEADER}")
		if (${HEADER} MATCHES "${CMAKE_BINARY_DIR}.*")
			STRING(REGEX REPLACE "${CMAKE_BINARY_DIR}/uscxml/" "" REL_HEADER ${HEADER})
			STRING(REGEX MATCH "[^/\\](.*)[/\\]" REL_HEADER ${REL_HEADER})
			SET(REL_HEADER "uscxml/${REL_HEADER}")
#			message(STATUS "MATCHED CMAKE_BINARY_DIR -> ${REL_HEADER}")
		elseif(${HEADER} MATCHES "${PROJECT_SOURCE_DIR}.*")
			STRING(REGEX REPLACE "${PROJECT_SOURCE_DIR}/src/" "" REL_HEADER ${HEADER})
#			message(STATUS "MATCHED PROJECT_SOURCE_DIR -> ${REL_HEADER}")
		else()
			message(STATUS "MATCHED no known prefix: ${HEADER}")
		endif()
		STRING(REGEX MATCH "(.*)[/\\]" DIR ${REL_HEADER})
#			message("ADDING ${HEADER} in include/${DIR} for ${INSTALL_HEADERS_COMPONENT}")
			INSTALL(FILES ${HEADER} DESTINATION include/${DIR} COMPONENT ${INSTALL_HEADERS_COMPONENT})
	ENDFOREACH()
endfunction()

function(INSTALL_FILES)
	set(options)
	set(oneValueArgs COMPONENT DESTINATION)
	set(multiValueArgs FILES)
	cmake_parse_arguments(INSTALL_FILE "${options}" "${oneValueArgs}" "${multiValueArgs}" ${ARGN})
	install(FILES ${INSTALL_FILE_FILES} DESTINATION ${INSTALL_FILE_DESTINATION} COMPONENT ${INSTALL_FILE_COMPONENT})
endfunction()

function(INSTALL_LIBRARY)
	set(options)
	set(oneValueArgs COMPONENT)
	set(multiValueArgs TARGETS)
	cmake_parse_arguments(INSTALL_LIBRARY "${options}" "${oneValueArgs}" "${multiValueArgs}" ${ARGN})
	install(TARGETS ${INSTALL_LIBRARY_TARGETS} DESTINATION lib COMPONENT ${INSTALL_LIBRARY_COMPONENT})
endfunction()

function(INSTALL_EXECUTABLE)
	set(options)
	set(oneValueArgs COMPONENT)
	set(multiValueArgs TARGETS)
	cmake_parse_arguments(INSTALL_EXECUTABLE "${options}" "${oneValueArgs}" "${multiValueArgs}" ${ARGN})
	install(
		TARGETS ${INSTALL_EXECUTABLE_TARGETS} 
		DESTINATION bin
		COMPONENT ${INSTALL_EXECUTABLE_COMPONENT}
		PERMISSIONS WORLD_EXECUTE OWNER_EXECUTE GROUP_EXECUTE OWNER_WRITE OWNER_READ GROUP_READ WORLD_READ)
endfunction()

# see http://www.cmake.org/Wiki/CMakeCompareVersionStrings
SET(THREE_PART_VERSION_REGEX "[0-9]+\\.[0-9]+\\.[0-9]+")
SET(TWO_PART_VERSION_REGEX "[0-9]+\\.[0-9]+")

# Breaks up a string in the form n1.n2.n3 into three parts and stores
# them in major, minor, and patch.  version should be a value, not a
# variable, while major, minor and patch should be variables.

MACRO(THREE_PART_VERSION_TO_VARS version major minor patch)
  IF(${version} MATCHES ${THREE_PART_VERSION_REGEX})
    STRING(REGEX REPLACE "^([0-9]+)\\.[0-9]+\\.[0-9]+" "\\1" ${major} "${version}")
    STRING(REGEX REPLACE "^[0-9]+\\.([0-9]+)\\.[0-9]+" "\\1" ${minor} "${version}")
    STRING(REGEX REPLACE "^[0-9]+\\.[0-9]+\\.([0-9]+)" "\\1" ${patch} "${version}")
  ELSEIF(${version} MATCHES ${TWO_PART_VERSION_REGEX})
    STRING(REGEX REPLACE "^([0-9]+)\\.[0-9]+" "\\1" ${major} "${version}")
    STRING(REGEX REPLACE "^[0-9]+\\.([0-9])+" "\\1" ${minor} "${version}")
  ELSE(${version} MATCHES ${THREE_PART_VERSION_REGEX})
    MESSAGE("MACRO(THREE_PART_VERSION_TO_VARS ${version} ${major} ${minor} ${patch}")
    MESSAGE(FATAL_ERROR "Problem parsing version string, I can't parse it properly.")
  ENDIF(${version} MATCHES ${THREE_PART_VERSION_REGEX})
ENDMACRO(THREE_PART_VERSION_TO_VARS)


MACRO(CHECK_COMPILER_FEATURE feature output)
	if (";${CMAKE_CXX_COMPILE_FEATURES};" MATCHES ";${feature};")
		set(${output} ON)
	else()
		set(${output} OFF)		
	endif()
	
ENDMACRO(CHECK_COMPILER_FEATURE)


#
# http://stackoverflow.com/questions/15706318/check-if-cmake-module-exists
#
# This makes use of the fact that if a package configuration file isn't found
# for VAR, then a cache variable VAR_DIR is set to VAR_DIR-NOTFOUND. So if the
# package configuration file is found, either this variable isn't defined, or
# it's set to a valid path (regardless of whether the find_package finds the
# requested package).

function(CheckHasModule Module)
  find_package(${Module} QUIET)
  if(NOT DEFINED ${Module}_DIR)
    set(HAS_MODULE_${Module} TRUE PARENT_SCOPE)
  elseif(${Module}_DIR)
    set(HAS_MODULE_${Module} TRUE PARENT_SCOPE)
  else()
    set(HAS_MODULE_${Module} FALSE PARENT_SCOPE)
  endif()
endfunction()
