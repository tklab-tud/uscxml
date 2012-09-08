# generate JNI library and create a jar
# Make from within Eclipse fails miserably with the whole thing

find_package(JNI)
if(JNI_FOUND)
	include_directories(${JNI_INCLUDE_DIRS})
else()
	message(STATUS "No JNI libraries found - not building Java wrappers")
	return()
endif()

include_directories(${CMAKE_CURRENT_SOURCE_DIR})

SET(CMAKE_SWIG_FLAGS "")
SET(SCXMLPL_JAVA_PACKAGE "org.uscxml")
SET(SCXMLPL_JAVA_DIR "org/uscxml")

# we need ; to produce a space with the package .. weird
SET_SOURCE_FILES_PROPERTIES(uscxml.i PROPERTIES SWIG_FLAGS "-package;${SCXMLPL_JAVA_PACKAGE}")
SET_SOURCE_FILES_PROPERTIES(uscxml.i PROPERTIES CPLUSPLUS ON)
SET(CMAKE_SWIG_OUTDIR "${CMAKE_CURRENT_BINARY_DIR}/${SCXMLPL_JAVA_DIR}")

SWIG_ADD_MODULE(uscxmlNativeJava java uscxml.i)
foreach(JNI_LIBRARY ${JNI_LIBRARIES})
	if (NOT ${JNI_LIBRARY} MATCHES ".*jawt.*")
		SWIG_LINK_LIBRARIES(uscxmlNativeJava ${JNI_LIBRARY})
	endif()
endforeach()
set_target_properties(uscxmlNativeJava PROPERTIES FOLDER "Bindings")

swig_link_libraries(uscxmlNativeJava uscxml)
