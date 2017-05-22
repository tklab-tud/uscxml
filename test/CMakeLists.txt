set(TEST_TIMEOUT 30)
set(CTEST_TEST_TIMEOUT 30)
set(TEST_BENCHMARK_ITERATIONS 1000)

find_program(SPIN_BIN spin)
find_program(CC_BIN gcc)
find_program(CXX_BIN g++)
find_program(ANT_BIN ant)
if (NOT ANT_BIN)
	message(STATUS "No ant binary found, not generating Java tests / bindings")
endif()
find_program(PERL_BIN perl)
find_program(PYTHON_BIN python)
find_program(GHDL_BIN ghdl)

set(GHDL_VERSION "0")
if (GHDL_BIN)
	execute_process(COMMAND ${GHDL_BIN} -v OUTPUT_VARIABLE GHDL_VERSION_OUT)
	string(REGEX REPLACE "^GHDL " "" GHDL_VERSION_OUT ${GHDL_VERSION_OUT})
	string(REGEX MATCH "^([0-9]+\\.[0-9]+)" GHDL_VERSION ${GHDL_VERSION_OUT})

	if (${GHDL_VERSION} VERSION_LESS "0.32")
		message(STATUS "GHDL version 0.32 required - ${GHDL_VERSION} found, not building VHDL tests")
		unset(GHDL_BIN)
	endif ()
endif ()

function(USCXML_TEST_COMPILE)
	set(options BUILD_ONLY)
	set(oneValueArgs LABEL NAME)
	set(multiValueArgs FILES ARGS)
	cmake_parse_arguments(USCXML_TEST "${options}" "${oneValueArgs}" "${multiValueArgs}" ${ARGN})

	list(APPEND USCXML_TEST_FILES ${GETOPT_FILES})

	add_executable(${USCXML_TEST_NAME} ${USCXML_TEST_FILES})
	target_link_libraries(${USCXML_TEST_NAME} uscxml)
	if (NOT ${USCXML_TEST_BUILD_ONLY})
		add_test(${USCXML_TEST_NAME} ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/${USCXML_TEST_NAME} ${USCXML_TEST_ARGS})
		set_property(TEST ${USCXML_TEST_NAME} PROPERTY LABELS ${USCXML_TEST_LABEL})
		set_property(TEST ${USCXML_TEST_NAME} PROPERTY TIMEOUT ${TEST_TIMEOUT})
		set_property(TEST ${USCXML_TEST_NAME} PROPERTY ENVIRONMENT "USCXML_PLUGIN_PATH=${CMAKE_BINARY_DIR}/lib/plugins")
	endif ()
	set_target_properties(${USCXML_TEST_NAME} PROPERTIES FOLDER "Tests")
endfunction()

# simple one file tests
USCXML_TEST_COMPILE(NAME test-utils LABEL general/test-utils FILES src/test-utils.cpp)
if(WITH_DM_LUA AND NOT BUILD_AS_PLUGINS)
	USCXML_TEST_COMPILE(
		NAME test-extensions 
		LABEL general/test-extensions 
		FILES 
			src/test-extensions.cpp 
			../contrib/src/uscxml/PausableDelayedEventQueue.cpp 
			../contrib/src/uscxml/ExtendedLuaDataModel.cpp
			../contrib/src/uscxml/CustomExecutableContent.cpp)
endif()
USCXML_TEST_COMPILE(NAME test-url LABEL general/test-url FILES src/test-url.cpp)
USCXML_TEST_COMPILE(NAME test-lifecycle LABEL general/test-lifecycle FILES src/test-lifecycle.cpp)
USCXML_TEST_COMPILE(NAME test-validating LABEL general/test-validating FILES src/test-validating.cpp)
USCXML_TEST_COMPILE(NAME test-snippets LABEL general/test-snippets FILES src/test-snippets.cpp)

if (NOT BUILD_AS_PLUGINS)
	USCXML_TEST_COMPILE(
		NAME test-serialization 
		LABEL general/test-serialization 
		FILES src/test-serialization.cpp ../contrib/src/uscxml/PausableDelayedEventQueue.cpp
		ARGS ${CMAKE_CURRENT_SOURCE_DIR}/w3c/ecma)
endif()
# USCXML_TEST_COMPILE(NAME test-c89-parser LABEL general/test-c89-parser FILES src/test-c89-parser.cpp)

# test-stress is not an automated test
if (NOT BUILD_AS_PLUGINS)
	USCXML_TEST_COMPILE(BUILD_ONLY NAME test-stress LABEL general/test-stress FILES src/test-stress.cpp)
endif()

file(GLOB_RECURSE USCXML_WRAPPERS
		${PROJECT_SOURCE_DIR}/src/bindings/swig/wrapped/*.cpp
		${PROJECT_SOURCE_DIR}/src/bindings/swig/wrapped/*.h
)

USCXML_TEST_COMPILE(NAME test-bindings LABEL general/test-bindings FILES ${USCXML_WRAPPERS} src/test-bindings.cpp)
if (NOT MSVC)
	# MSVC does not like to redefine 'protected'
	USCXML_TEST_COMPILE(NAME test-promela-parser LABEL general/test-promela-parser FILES src/test-promela-parser.cpp)
	target_link_libraries(test-promela-parser uscxml_transform)
endif ()

# the one binary to test for pass / fail final states
add_executable(test-state-pass src/test-state-pass.cpp ${GETOPT_FILES})
target_link_libraries(test-state-pass uscxml)
set_target_properties(test-state-pass PROPERTIES FOLDER "Tests")

if (WIN32 AND BUILD_SHARED_LIBS)
	# do not build test-gen-c on windows with shared libraries active
	# due to __declspec(dllexport) being activated. We would need to
	# drop the USCXML_EXPORT definition for this target
elseif (BUILD_AS_PLUGINS)
	# Just too much of a macro mess to support for now
else()
	set(TEST_GEN_C_DEFINITIONS "NO_XERCESC" "FEATS_ON_CMD")
	set(TEST_GEN_C_LIBRARIES ${LIBEVENT_LIBRARIES})
	set(TEST_GEN_C_FILES
		src/test-gen-c.cpp
		${PROJECT_SOURCE_DIR}/src/uscxml/interpreter/BasicDelayedEventQueue.cpp
		${PROJECT_SOURCE_DIR}/src/uscxml/interpreter/BasicEventQueue.cpp
		${PROJECT_SOURCE_DIR}/src/uscxml/interpreter/EventQueue.cpp
		${PROJECT_SOURCE_DIR}/src/uscxml/interpreter/ContentExecutor.cpp
		${PROJECT_SOURCE_DIR}/src/uscxml/interpreter/MicroStep.cpp
		${PROJECT_SOURCE_DIR}/src/uscxml/interpreter/Logging.cpp
		${PROJECT_SOURCE_DIR}/src/uscxml/interpreter/StdOutLogger.cpp
		${PROJECT_SOURCE_DIR}/src/uscxml/util/UUID.cpp
		${PROJECT_SOURCE_DIR}/src/uscxml/util/Convenience.cpp
		${PROJECT_SOURCE_DIR}/src/uscxml/util/Base64.c
		${PROJECT_SOURCE_DIR}/src/uscxml/util/MD5.c
		${PROJECT_SOURCE_DIR}/src/uscxml/util/SHA1.c
		${PROJECT_SOURCE_DIR}/src/uscxml/messages/Data.cpp
		${PROJECT_SOURCE_DIR}/src/uscxml/messages/Event.cpp
		${PROJECT_SOURCE_DIR}/src/uscxml/messages/Blob.cpp
		${PROJECT_SOURCE_DIR}/src/uscxml/plugins/Factory.cpp
		${PROJECT_SOURCE_DIR}/src/uscxml/plugins/DataModel.cpp
		${PROJECT_SOURCE_DIR}/src/uscxml/plugins/Invoker.cpp
		${PROJECT_SOURCE_DIR}/src/uscxml/plugins/IOProcessor.cpp
		${PROJECT_SOURCE_DIR}/src/uscxml/plugins/datamodel/null/NullDataModel.cpp
	  ${PROJECT_SOURCE_DIR}/contrib/src/jsmn/jsmn.c
	  ${PROJECT_SOURCE_DIR}/contrib/src/evws/evws.c
		${GETOPT_FILES})
	
	if (${WITH_DM_ECMA_V8})
		list (APPEND TEST_GEN_C_DEFINITIONS "WITH_DM_ECMA_V8")
		list (APPEND TEST_GEN_C_FILES ${PROJECT_SOURCE_DIR}/src/uscxml/plugins/datamodel/ecmascript/v8/V8DataModel.cpp)
		list (APPEND TEST_GEN_C_LIBRARIES ${V8_LIBRARY})
	endif()
	if (${WITH_DM_ECMA_JSC})
		list (APPEND TEST_GEN_C_DEFINITIONS "WITH_DM_ECMA_JSC")
		list (APPEND TEST_GEN_C_FILES ${PROJECT_SOURCE_DIR}/src/uscxml/plugins/datamodel/ecmascript/JavaScriptCore/JSCDataModel.cpp)
		list (APPEND TEST_GEN_C_LIBRARIES ${JSC_LIBRARY})
	endif()
	if (${WITH_DM_LUA})
		list (APPEND TEST_GEN_C_DEFINITIONS "WITH_DM_LUA")
		list (APPEND TEST_GEN_C_FILES ${PROJECT_SOURCE_DIR}/src/uscxml/plugins/datamodel/lua/LuaDataModel.cpp)
		list (APPEND TEST_GEN_C_LIBRARIES ${LUA_LIBRARIES})
	endif()
	if (${WITH_DM_PROMELA})
		list (APPEND TEST_GEN_C_DEFINITIONS "WITH_DM_PROMELA")
		list (APPEND TEST_GEN_C_FILES 
			${PROJECT_SOURCE_DIR}/src/uscxml/plugins/datamodel/promela/PromelaDataModel.cpp
			${PROJECT_SOURCE_DIR}/src/uscxml/plugins/datamodel/promela/PromelaParser.cpp
			${PROJECT_SOURCE_DIR}/src/uscxml/plugins/datamodel/promela/parser/promela.lex.yy.cpp
			${PROJECT_SOURCE_DIR}/src/uscxml/plugins/datamodel/promela/parser/promela.tab.cpp
			${PROJECT_SOURCE_DIR}/src/uscxml/plugins/datamodel/promela/parser/promela.lex.yy.cpp
		)
	endif()

	add_executable(test-gen-c ${TEST_GEN_C_FILES})
	target_link_libraries(test-gen-c ${TEST_GEN_C_LIBRARIES})
	# target_link_libraries(test-gen-c ${XercesC_LIBRARIES} ${LIBEVENT_LIBRARIES} ${CURL_LIBRARIES})

	if (USCXML_PREREQS)
	    add_dependencies(test-gen-c ${USCXML_PREREQS})
	endif()

	if (WIN32)
		target_link_libraries(test-gen-c Ws2_32)	
	endif()
	if (UNIX)
		target_link_libraries(test-gen-c pthread)
	endif()
	set_target_properties(test-gen-c PROPERTIES FOLDER "Tests")
	set_target_properties(test-gen-c PROPERTIES COMPILE_DEFINITIONS "${TEST_GEN_C_DEFINITIONS}")
	# set_target_properties(test-gen-c PROPERTIES COMPILE_DEFINITIONS "NO_XERCESC;FEATS_ON_CMD")
endif()

# issues
file(GLOB_RECURSE USCXML_ISSUES
		issues/*.cpp
		issues/*.scxml
		)
foreach (USCXML_ISSUE ${USCXML_ISSUES})
	get_filename_component(ISSUE_NAME ${USCXML_ISSUE} NAME_WE)
	get_filename_component(ISSUE_TYPE ${USCXML_ISSUE} EXT)
	if (ISSUE_TYPE STREQUAL ".scxml")
		add_test(issue/${ISSUE_NAME} ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-state-pass ${USCXML_ISSUE})
		set_property(TEST issue/${ISSUE_NAME} PROPERTY LABELS issue/${ISSUE_NAME})
		set_property(TEST issue/${ISSUE_NAME} PROPERTY ENVIRONMENT "USCXML_PLUGIN_PATH=${CMAKE_BINARY_DIR}/lib/plugins")
	else ()
		USCXML_TEST_COMPILE(NAME ${ISSUE_NAME} LABEL issues/${ISSUE_NAME} FILES ${USCXML_ISSUE})
	endif ()
endforeach ()

# make sure the important headers are self-reliant
set(USCXML_PUBLIC_HEADERS
		"${PROJECT_SOURCE_DIR}/src/uscxml/uscxml.h"
		"${PROJECT_SOURCE_DIR}/src/uscxml/Interpreter.h"
	)

file(GLOB_RECURSE USCXML_HEADERS
		../src/*.h
		../src/*.hpp
		)

foreach (USCXML_HEADER ${USCXML_PUBLIC_HEADERS})
	# message (STATUS "USCXML_HEADER: ${USCXML_HEADER}")
	# message (STATUS "USCXML_REL_HEADER: ${USCXML_REL_HEADER}")
	# message (STATUS "CMAKE_CURRENT_SOURCE_DIR: ${CMAKE_CURRENT_SOURCE_DIR}")
	STRING(REGEX REPLACE "${PROJECT_SOURCE_DIR}/src/" "" USCXML_REL_HEADER ${USCXML_HEADER})

	set(HEADER_TEST)
	set(HEADER_TEST "${HEADER_TEST}#include \"${USCXML_HEADER}\"\n")
	set(HEADER_TEST "${HEADER_TEST}int main(int argc, char** argv) {}")
	FILE(WRITE ${CMAKE_CURRENT_BINARY_DIR}/headers/${USCXML_REL_HEADER}.cpp ${HEADER_TEST})

	add_test(NAME "header/${USCXML_REL_HEADER}"
			COMMAND ${CMAKE_COMMAND}
			-DTESTFILE:FILEPATH=${CMAKE_CURRENT_BINARY_DIR}/headers/${USCXML_REL_HEADER}.cpp
			-DCC_BIN:FILEPATH=${CC_BIN}
			-DCXX_BIN:FILEPATH=${CXX_BIN}
			-DPROJECT_SOURCE_DIR=${PROJECT_SOURCE_DIR}
			-DUSCXML_PLATFORM_ID=${USCXML_PLATFORM_ID}
			-DCMAKE_BINARY_DIR=${CMAKE_BINARY_DIR}
			-DPROJECT_BINARY_DIR=${PROJECT_BINARY_DIR}
			-DCMAKE_LIBRARY_OUTPUT_DIRECTORY=${CMAKE_LIBRARY_OUTPUT_DIRECTORY}
			-P ${CMAKE_CURRENT_SOURCE_DIR}/ctest/scripts/run_header_compiles.cmake)
	set_property(TEST "header/${USCXML_REL_HEADER}" PROPERTY LABELS "header/${USCXML_REL_HEADER}")
	set_property(TEST "header/${USCXML_REL_HEADER}" PROPERTY ENVIRONMENT "USCXML_PLUGIN_PATH=${CMAKE_BINARY_DIR}/lib/plugins")

endforeach ()

# debugger REST API
if (PERL_BIN)
	add_test(NAME "general/test-debug-api"
			COMMAND ${PERL_BIN}
			"${PROJECT_SOURCE_DIR}/test/src/test-http-debugger.pl"
			"${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/uscxml-browser"
			WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}/test/src
			)
	set_property(TEST "general/test-debug-api" PROPERTY LABELS "general/test-debug-api")
	set_property(TEST "general/test-debug-api" PROPERTY DEPENDS uscxml-browser)
	set_property(TEST "general/test-debug-api" PROPERTY ENVIRONMENT "USCXML_PLUGIN_PATH=${CMAKE_BINARY_DIR}/lib/plugins")

endif ()

# declare W3C tests

if (NOT BUILD_MINIMAL)
	# copy resources
	file(GLOB_RECURSE W3C_RESOURCES
			w3c/*.txt
			w3c/*sub*.scxml
			)

	set(TEST_CLASSES
			# standard tests generated per datamodel
			"namespace"
			"ecma"
			# "xpath"
			"null"
			"lua"
			"promela"

			# generated c source
			"gen/c/ecma"
			# "gen/c/xpath"
			"gen/c/lua"
			# "gen/c/promela"
			# "gen/vhdl/ecma"
			"gen/vhdl/promela"
			"gen/vhdl/null"

			"gen/java/jexl"

			# bindings
			"binding/java/jexl"
			"binding/python/ecma"

			# state-machine interpreters
			# "fsm/ecma"
			# "fsm/xpath"
			# "fsm/lua"
			# "fsm/promela"

			# formal verification
			"spin/promela"

			# performance tests
			# "perf/gen/c/ecma"
			# "perf/ecma"
			)
	if (WITH_DM_C89)
		LIST(APPEND TEST_CLASSES c89)
	endif()

	# prepare directories for test classes and copy resources over
	foreach (W3C_RESOURCE ${W3C_RESOURCES})
		get_filename_component(TEST_DATAMODEL ${W3C_RESOURCE} PATH)
		get_filename_component(TEST_DATAMODEL ${TEST_DATAMODEL} NAME)

		# message(STATUS "W3C_RESOURCE: ${W3C_RESOURCE}")
		# message(STATUS "TEST_DATAMODEL: ${TEST_DATAMODEL}")

		foreach (TEST_CLASS ${TEST_CLASSES})
			# datamodel has to be the suffix of the test class
			if (TEST_CLASS MATCHES ".*/${TEST_DATAMODEL}$")
				file(COPY ${W3C_RESOURCE} DESTINATION ${CMAKE_CURRENT_BINARY_DIR}/${TEST_CLASS})
			endif ()
		endforeach ()
	endforeach ()

	# establish actual tests
	foreach (TEST_CLASS ${TEST_CLASSES})
		get_filename_component(TEST_DATAMODEL ${TEST_CLASS} NAME)
		get_filename_component(TEST_TYPE ${TEST_CLASS} PATH)

		# get all respective scxml files into W3C_TESTS
		file(GLOB_RECURSE W3C_TESTS w3c/${TEST_DATAMODEL}/*.scxml)

		SET(IS_PERFORMANCE_TEST OFF)
		if (TEST_CLASS MATCHES "^perf/.*")
			SET(IS_PERFORMANCE_TEST ON)
		endif ()

		if (IS_PERFORMANCE_TEST)
			string(REGEX REPLACE "^perf/?" "" TEST_TYPE ${TEST_TYPE})
		endif ()

		SET(IS_STANDARD_TEST OFF)
		if ("${TEST_TYPE}" STREQUAL "")
			if (IS_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/w3c/${TEST_DATAMODEL}")
				SET(IS_STANDARD_TEST ON)
			endif ()
		endif ()

		# normal IRP tests - get all scxml files within
		foreach (W3C_TEST ${W3C_TESTS})
			set(TEST_ADDED OFF)
			get_filename_component(TEST_FILE ${W3C_TEST} NAME)
			set(TEST_NAME "w3c/${TEST_CLASS}/${TEST_FILE}")

			if (OFF)
				# manual tests:
			elseif (TEST_FILE STREQUAL "test307.scxml")
				# scxml files, but no proper tests:
			elseif (TEST_NAME MATCHES ".*sub.*")
				# rest is a proper test:
			else ()

				if (IS_STANDARD_TEST)

					add_test(${TEST_NAME} ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-state-pass ${W3C_TEST})
					set(TEST_ADDED ON)

					if (TEST_NAME MATCHES ".*/test250.scxml")
						set_tests_properties(${TEST_NAME} PROPERTIES FAIL_REGULAR_EXPRESSION "entering final state, invocation was not cancelled")
					elseif (TEST_NAME MATCHES ".*/test307.scxml")
						set_tests_properties(${TEST_NAME} PROPERTIES FAIL_REGULAR_EXPRESSION "error in state")
					endif ()

					# more properties for standard tests

				elseif (TEST_TYPE MATCHES "^gen.*")
					# tests for generated languages via ctest/scripts/test_generated_${TEST_TARGET}.cmake
					get_filename_component(TEST_TARGET ${TEST_TYPE} NAME)
					if (TEST_TYPE MATCHES "^gen/${TEST_TARGET}")

						# a few necessary preconditions per target language
						if (TEST_TARGET MATCHES "vhdl" AND "${GHDL_VERSION}" VERSION_LESS "0.32")
							break()
						endif()

						if (TEST_TARGET MATCHES "java" AND NOT ANT_BIN)
							break()
						endif()

						# call test script
						add_test(NAME "${TEST_NAME}"
								COMMAND ${CMAKE_COMMAND}
								-DOUTDIR:FILEPATH=${CMAKE_CURRENT_BINARY_DIR}/${TEST_CLASS}
								-DTESTFILE:FILEPATH=${W3C_TEST}
								-DTARGETLANG=${TEST_TARGET}
								-DWITH_DM_ECMA_JSC:BOOL=${WITH_DM_ECMA_JSC}
								-DJSC_INCLUDE_DIR:BOOL=${JSC_INCLUDE_DIR}
								-DJSC_LIBRARY:FILEPATH=${JSC_LIBRARY}
								-DWITH_DM_ECMA_V8:BOOL=${WITH_DM_ECMA_V8}
								-DV8_LIBRARY:FILEPATH=${V8_LIBRARY}
								-DV8_INCLUDE_DIR:BOOL=${V8_INCLUDE_DIR}
								-DWITH_DM_LUA:BOOL=${WITH_DM_LUA}
								-DLUA_LIBRARIES:FILEPATH=${LUA_LIBRARIES}
								-DLUA_INCLUDE_DIR:FILEPATH=${LUA_INCLUDE_DIR}
								-DUSCXML_TRANSFORM_BIN:FILEPATH=${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/uscxml-transform
								-DANT_BIN:FILEPATH=${ANT_BIN}
								-DCC_BIN:FILEPATH=${CC_BIN}
								-DCXX_BIN:FILEPATH=${CXX_BIN}
								-DGHDL_BIN:FILEPATH=${GHDL_BIN}
								-DPROJECT_SOURCE_DIR=${PROJECT_SOURCE_DIR}
								-DUSCXML_PLATFORM_ID=${USCXML_PLATFORM_ID}
								-DCMAKE_BINARY_DIR=${CMAKE_BINARY_DIR}
								-DPROJECT_BINARY_DIR=${PROJECT_BINARY_DIR}
								-DXercesC_INCLUDE_DIRS=${XercesC_INCLUDE_DIRS}
								-DURIPARSER_INCLUDE_DIR=${URIPARSER_INCLUDE_DIR}
								-DLIBEVENT_INCLUDE_DIR=${LIBEVENT_INCLUDE_DIR}
								-DCMAKE_LIBRARY_OUTPUT_DIRECTORY=${CMAKE_LIBRARY_OUTPUT_DIRECTORY}
								-DSCAFFOLDING_FOR_GENERATED_C:FILEPATH=${CMAKE_CURRENT_SOURCE_DIR}/src/test-gen-c.cpp
								-P ${CMAKE_CURRENT_SOURCE_DIR}/ctest/scripts/test_generated_${TEST_TARGET}.cmake)
						set_property(TEST ${TEST_NAME} PROPERTY DEPENDS uscxml-transform)
						set(TEST_ADDED ON)
					endif()

				elseif (TEST_TYPE MATCHES "^binding.*")
					get_filename_component(TEST_LANG ${TEST_TYPE} NAME)

					if (TARGET jar AND TEST_LANG STREQUAL "java")
						add_test(NAME "${TEST_NAME}"
								COMMAND
								${ANT_BIN}
								-Dtest.file=${W3C_TEST}
								-Duscxml.jar=${CMAKE_LIBRARY_OUTPUT_DIRECTORY}/uscxml.jar
								WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}/contrib/java/bindings)
						set_property(TEST ${TEST_NAME} PROPERTY DEPENDS jar)
						set(TEST_ADDED ON)
					endif ()

					if (PYTHON_BIN AND TEST_LANG STREQUAL "python")
						add_test(NAME "${TEST_NAME}"
								COMMAND
								${PYTHON_BIN}
								${PROJECT_SOURCE_DIR}/contrib/python/bindings/test-state-pass.py
								${W3C_TEST}
								WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}/contrib/python/bindings)
						
						set_property(TEST ${TEST_NAME} PROPERTY ENVIRONMENT "USCXML_PYTHON_PATH=${CMAKE_LIBRARY_OUTPUT_DIRECTORY}")
						set_property(TEST ${TEST_NAME} APPEND PROPERTY ENVIRONMENT "USCXML_PLUGIN_PATH=${CMAKE_BINARY_DIR}/lib/plugins")
						set(TEST_ADDED ON)
					endif ()

				elseif (TEST_TYPE MATCHES "^spin.*")

					if (NOT ${TEST_DATAMODEL} STREQUAL "promela")
						break()
					endif ()

					add_test(NAME "${TEST_NAME}"
							COMMAND ${CMAKE_COMMAND}
							-DOUTDIR:FILEPATH=${CMAKE_CURRENT_BINARY_DIR}/promela
							-DTESTFILE:FILEPATH=${W3C_TEST}
							-DUSCXML_TRANSFORM_BIN:FILEPATH=${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/uscxml-transform
							-DSPIN_BIN:FILEPATH=${SPIN_BIN}
							-DCC_BIN:FILEPATH=${CC_BIN}
							-P ${CMAKE_CURRENT_SOURCE_DIR}/ctest/scripts/run_promela_test.cmake)
					set_property(TEST ${TEST_NAME} PROPERTY PASS_REGULAR_EXPRESSION "depth reached [0-9]+, errors: 0")
					set_property(TEST ${TEST_NAME} PROPERTY FAIL_REGULAR_EXPRESSION "depth reached [0-9]+, errors: [1-9]+")
					set(TEST_ADDED ON)

				elseif (TEST_TYPE MATCHES "^fsm.*")

					add_test("${TEST_NAME}" ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-state-pass -f ${W3C_TEST})
					set(TEST_ADDED ON)

				endif ()

				if (TEST_ADDED)
					set_property(TEST ${TEST_NAME} PROPERTY LABELS ${TEST_NAME})
					set_property(TEST ${TEST_NAME} PROPERTY TIMEOUT ${TEST_TIMEOUT})
					set_property(TEST ${TEST_NAME} APPEND PROPERTY ENVIRONMENT "USCXML_PLUGIN_PATH=${CMAKE_BINARY_DIR}/lib/plugins")
					if (IS_PERFORMANCE_TEST)
						set_property(TEST ${TEST_NAME} APPEND PROPERTY ENVIRONMENT USCXML_BENCHMARK_ITERATIONS=${TEST_BENCHMARK_ITERATIONS})
					endif ()
				endif ()

			endif ()
		endforeach ()
	endforeach ()

endif ()
