# generate PHP module

find_package(PHP5)
if(PHP5_FOUND)
	include_directories(${PHP5_INCLUDE_PATH})
else()
	message(STATUS "No PHP5 libraries found - not building php module")
	return()
endif()

#message(FATAL_ERROR "PHP_LDFLAGS: ${PHP_LDFLAGS}")

include_directories(${CMAKE_CURRENT_SOURCE_DIR})
include_directories(${PHP_INCLUDE_DIRS})

SET(CMAKE_SWIG_FLAGS "")

# we need ; to produce a space with the package .. weird
SET_SOURCE_FILES_PROPERTIES(uscxml.i PROPERTIES CPLUSPLUS ON)

SWIG_ADD_MODULE(uscxmlNativePHP php5 uscxml.i)
foreach(PHP_LIBRARY ${PHP_LIBRARIES})
	SWIG_LINK_LIBRARIES(uscxmlNativePHP ${PHP_LIBRARY})
endforeach()

#set_target_properties(uscxmlNativePHP PROPERTIES LINK_FLAGS ${PHP_LDFLAGS})
set_target_properties(uscxmlNativePHP PROPERTIES FOLDER "Bindings")

SWIG_LINK_LIBRARIES(uscxmlNativePHP uscxml)
