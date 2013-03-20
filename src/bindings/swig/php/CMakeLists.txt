# generate PHP module

find_package(PHP5)
if(PHP5_FOUND)
	include_directories(${PHP5_INCLUDE_PATH})
else()
	message(STATUS "No PHP5 libraries found - not building php module")
	return()
endif()

include_directories(${CMAKE_CURRENT_SOURCE_DIR})

SET(CMAKE_SWIG_FLAGS "")

# we need ; to produce a space with the package .. weird
# SET_SOURCE_FILES_PROPERTIES(uscxml.i PROPERTIES SWIG_FLAGS "-package;${SCXMLPL_JAVA_PACKAGE}")
SET_SOURCE_FILES_PROPERTIES(uscxml.i PROPERTIES CPLUSPLUS ON)
SET(CMAKE_SWIG_OUTDIR "${CMAKE_CURRENT_BINARY_DIR}/${SCXMLPL_JAVA_DIR}")

SWIG_ADD_MODULE(uscxmlNativePHP php uscxml.i)
# foreach(JNI_LIBRARY ${JNI_LIBRARIES})
# 	if (NOT ${JNI_LIBRARY} MATCHES ".*jawt.*")
# 		SWIG_LINK_LIBRARIES(uscxmlNativePHP ${JNI_LIBRARY})
# 	endif()
# endforeach()
set_target_properties(uscxmlNativePHP PROPERTIES FOLDER "Bindings")

swig_link_libraries(uscxmlNativePHP uscxml)
