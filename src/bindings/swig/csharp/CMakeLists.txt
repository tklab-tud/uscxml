# generate JNI library and create a jar
# Make from within Eclipse fails miserably with the whole thing

if (WIN32)
	LIST(APPEND CMAKE_PROGRAM_PATH "C:/Windows/Microsoft.NET/Framework/v3.5") # CSharp compiler
	LIST(APPEND CMAKE_PROGRAM_PATH "C:/Windows/Microsoft.NET/Framework/v4.0.30319") # CSharp compiler
endif()

FIND_PROGRAM(DMCS_EXECUTABLE dmcs PATHS $ENV{DMCS_HOME} ENV PATH ) # Mono compiler
FIND_PROGRAM(CSC_EXECUTABLE csc PATHS $ENV{CSC_HOME} ENV PATH ) # CSharp compiler

if (DMCS_EXECUTABLE OR CSC_EXECUTABLE)
	# unset all library suffixes as swig will hardcode a library without
	SET(LIB_POSTFIX ${CMAKE_LIBRARY_POSTFIX})

	SET(CMAKE_DEBUG_POSTFIX "")
	SET(CMAKE_RELEASE_POSTFIX "")
	SET(CMAKE_RELWITHDEBINFO_POSTFIX "")
	SET(CMAKE_MINSIZEREL_POSTFIX "")
	SET(CMAKE_LIBRARY_POSTFIX "")

	if (MSVC)
		# MSVC does not include inttypes.h but SWIG needs it
		include_directories(${CMAKE_CURRENT_SOURCE_DIR}/../msvc)
	endif()

	include_directories(${CMAKE_CURRENT_SOURCE_DIR})

	SET(CMAKE_SWIG_FLAGS "")
	SET(USCXML_CSHARP_NAMESPACE "org.uscxml")
	SET(USCXML_CSHARP_DIR "org/uscxml")

	if (CMAKE_BUILD_TYPE STREQUAL "Debug")
		list(APPEND CMAKE_SWIG_FLAGS "-DDEBUG")
	endif()


	# we need ; to produce a space with the package .. weird
	SET_SOURCE_FILES_PROPERTIES(uscxml.i PROPERTIES SWIG_FLAGS "-w401;-namespace;${USCXML_CSHARP_NAMESPACE}")
	SET_SOURCE_FILES_PROPERTIES(uscxml.i PROPERTIES CPLUSPLUS ON)
	SET(CMAKE_SWIG_OUTDIR "${CMAKE_CURRENT_BINARY_DIR}/${USCXML_CSHARP_DIR}")

	set(USCXML_LANGUAGE_BINDINGS "csharp ${USCXML_LANGUAGE_BINDINGS}")

	SWIG_ADD_MODULE(uscxmlNativeCSharp csharp uscxml.i)
	set_target_properties(uscxmlNativeCSharp PROPERTIES FOLDER "Bindings")
	set_target_properties(uscxmlNativeCSharp
	    PROPERTIES
	    ARCHIVE_OUTPUT_DIRECTORY "${CMAKE_LIBRARY_OUTPUT_DIRECTORY}/csharp${LIB_POSTFIX}"
	    LIBRARY_OUTPUT_DIRECTORY "${CMAKE_LIBRARY_OUTPUT_DIRECTORY}/csharp${LIB_POSTFIX}"
	    RUNTIME_OUTPUT_DIRECTORY "${CMAKE_LIBRARY_OUTPUT_DIRECTORY}/csharp${LIB_POSTFIX}"
	)

	set_target_properties(uscxmlNativeCSharp PROPERTIES COMPILE_FLAGS "-DSWIG")
	swig_link_libraries(uscxmlNativeCSharp uscxml)
	
	# build managed code part
	if (CSC_EXECUTABLE)
		ADD_CUSTOM_TARGET(csharp
			COMMAND ${CMAKE_COMMAND} -E 
				copy ${CMAKE_CURRENT_SOURCE_DIR}/org/uscxml/InterpreterException.cs ${PROJECT_BINARY_DIR}/src/bindings/swig/csharp/org/uscxml
			COMMAND ${CSC_EXECUTABLE}
				/target:library
				/out:${CMAKE_LIBRARY_OUTPUT_DIRECTORY}/uscxmlCSharp.dll
				*.cs
				WORKING_DIRECTORY ${PROJECT_BINARY_DIR}/src/bindings/swig/csharp/org/uscxml
			COMMENT "Creating umundoCSharp.dll for C# ...")
	else()
		ADD_CUSTOM_TARGET(csharp
			COMMAND ${CMAKE_COMMAND} -E 
				copy ${CMAKE_CURRENT_SOURCE_DIR}/org/uscxml/InterpreterException.cs ${PROJECT_BINARY_DIR}/src/bindings/swig/csharp/org/uscxml
			COMMAND ${DMCS_EXECUTABLE}
				-target:library
				/out:${CMAKE_LIBRARY_OUTPUT_DIRECTORY}/uscxmlCSharp.dll
				*.cs
				WORKING_DIRECTORY ${PROJECT_BINARY_DIR}/src/bindings/swig/csharp/org/uscxml
			COMMENT "Creating umundoCSharp.dll for Mono ...")
	endif()
	
	add_dependencies(csharp uscxmlNativeCSharp)
	if (BUILD_TESTS)
		add_dependencies(ALL_TESTS csharp)
	endif()
	set_target_properties(csharp PROPERTIES FOLDER "Bindings")
	
	set(USCXML_LANGUAGE_BINDINGS ${USCXML_LANGUAGE_BINDINGS} PARENT_SCOPE)
else()	
	message(STATUS "Could not find dmcs or csc binary, not building csharp bindings")
endif()