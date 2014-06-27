# if you build swig from sources on windows, this is where it will end up
# see also: http://www.swig.org/Doc2.0/Windows.html#Windows_mingw_msys
if (CMAKE_CROSSCOMPILING)
	return()
endif()

if (WIN32)
	if(EXISTS "${PROJECT_BINARY_DIR}/../swig/")
		LIST(APPEND CMAKE_PROGRAM_PATH "${PROJECT_BINARY_DIR}/../swig/")
	elseif(EXISTS "${PROJECT_BINARY_DIR}/../../swig/")
		LIST(APPEND CMAKE_PROGRAM_PATH "${PROJECT_BINARY_DIR}/../../swig/")
	endif()

	LIST(APPEND CMAKE_PROGRAM_PATH "C:/Program Files/swig") # swig.exe
endif()
LIST(APPEND CMAKE_PROGRAM_PATH $ENV{SWIG_DIR})

find_package(SWIG)

if (SWIG_FOUND)
	if(SWIG_VERSION VERSION_GREATER 2.0.4)
		MARK_AS_ADVANCED(SWIG_DIR SWIG_EXECUTABLE SWIG_VERSION)
		INCLUDE(${SWIG_USE_FILE})
		add_subdirectory(swig/java)
		add_subdirectory(swig/csharp)
	else()
		message(STATUS "SWIG version 2.0.5 is required, found ${SWIG_VERSION} - skipping java wrapper generation")
	endif()
else()
	message(STATUS "SWIG not found - skipping wrapper generation")
endif()
set(USCXML_LANGUAGE_BINDINGS ${USCXML_LANGUAGE_BINDINGS} PARENT_SCOPE)
