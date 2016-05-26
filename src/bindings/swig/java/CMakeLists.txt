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
SET(USCXML_JAVA_PACKAGE "org.uscxml")
SET(USCXML_JAVA_DIR "org/uscxml")

# we need ; to produce a space with the package .. weird
SET_SOURCE_FILES_PROPERTIES(uscxml.i PROPERTIES SWIG_FLAGS "-w473;-package;${USCXML_JAVA_PACKAGE}")
SET_SOURCE_FILES_PROPERTIES(uscxml.i PROPERTIES CPLUSPLUS ON)
SET(CMAKE_SWIG_OUTDIR "${CMAKE_CURRENT_BINARY_DIR}/${USCXML_JAVA_DIR}")

SWIG_ADD_MODULE(uscxmlNativeJava java uscxml.i)
foreach(JNI_LIBRARY ${JNI_LIBRARIES})
	if (NOT ${JNI_LIBRARY} MATCHES ".*jawt.*")
		SWIG_LINK_LIBRARIES(uscxmlNativeJava ${JNI_LIBRARY})
	endif()
endforeach()
set_target_properties(uscxmlNativeJava PROPERTIES FOLDER "Bindings")
set_target_properties(uscxmlNativeJava PROPERTIES COMPILE_FLAGS "-DSWIG")

swig_link_libraries(uscxmlNativeJava uscxml)

file(GLOB POTENTIAL_ANT "C:/Program Files/apache-ant**/bin" "C:/Program Files (x86)/apache-ant**/bin")

FIND_PROGRAM(ANT_EXECUTABLE ant PATHS $ENV{ANT_HOME}/bin ${POTENTIAL_ANT} ENV PATH )
if (ANT_EXECUTABLE)
	set(USCXML_LANGUAGE_BINDINGS "java ${USCXML_LANGUAGE_BINDINGS}")
	
	set(JAR_EXCLUDE_DEBUG OFF)
	set(JAR_EXCLUDE_JNI OFF)
	
	# include all the JNI libraries prepared from DIST_PREPARE builds on the various desktop platforms
	if (DIST_PREPARE)
		if (CMAKE_CROSSCOMPILING)
			if (ANDROID)
				set(JAR_EXCLUDE_JNI ON) # JNI inside jar not allowed with Android
				SET(JAR_JNI_ROOT_PATH ${PROJECT_SOURCE_DIR}/package/cross-compiled/android)
			else()
				SET(JAR_JNI_ROOT_PATH ${PROJECT_SOURCE_DIR}/package/cross-compiled/${CMAKE_CROSSCOMPILING_TARGET_LC})
			endif()
		else()
			SET(JAR_JNI_ROOT_PATH ${PROJECT_SOURCE_DIR}/package)
		endif()
	else()
		# when not preparing a distribution, just put the jar into the libs
		SET(JAR_JNI_ROOT_PATH ${CMAKE_LIBRARY_OUTPUT_DIRECTORY})
	endif()
	
	ADD_CUSTOM_TARGET(java
		COMMAND ${ANT_EXECUTABLE}
		-Dlib.dir=${JAR_JNI_ROOT_PATH}
		-Dsrc.dir=${PROJECT_SOURCE_DIR}
		-Dbuild.dir=${PROJECT_BINARY_DIR}
		-Dbuild.type=${CMAKE_BUILD_TYPE}
		-Dexclude.debug=${JAR_EXCLUDE_DEBUG}
		-Dexclude.jni=${JAR_EXCLUDE_JNI}
		-f build-java.xml
		WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}/contrib/java
		COMMENT "Creating the jar ...")
	
	set_target_properties(java PROPERTIES FOLDER "Bindings")
else()
	message(STATUS "Could not find ant binary - will not build jars")
endif()

set(USCXML_LANGUAGE_BINDINGS ${USCXML_LANGUAGE_BINDINGS} PARENT_SCOPE)
