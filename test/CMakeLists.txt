set(TEST_TIMEOUT 30)
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
	endif ()
	set_target_properties(${USCXML_TEST_NAME} PROPERTIES FOLDER "Tests")
endfunction()

# simple one file tests
USCXML_TEST_COMPILE(NAME test-extensions LABEL general/test-extensions FILES src/test-extensions.cpp)
USCXML_TEST_COMPILE(NAME test-url LABEL general/test-url FILES src/test-url.cpp)
USCXML_TEST_COMPILE(NAME test-lifecycle LABEL general/test-lifecycle FILES src/test-lifecycle.cpp)
USCXML_TEST_COMPILE(NAME test-validating LABEL general/test-validating FILES src/test-validating.cpp)
USCXML_TEST_COMPILE(NAME test-snippets LABEL general/test-snippets FILES src/test-snippets.cpp)
# USCXML_TEST_COMPILE(NAME test-c89-parser LABEL general/test-c89-parser FILES src/test-c89-parser.cpp)

# test-stress is not an automated test
USCXML_TEST_COMPILE(BUILD_ONLY NAME test-stress LABEL general/test-stress FILES src/test-stress.cpp)

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

add_executable(test-gen-c src/test-gen-c.cpp ${GETOPT_FILES})
target_link_libraries(test-gen-c uscxml)
set_target_properties(test-gen-c PROPERTIES FOLDER "Tests")

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
	set_tests_properties("general/test-debug-api" PROPERTIES DEPENDS uscxml-browser)

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
			"c89"
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
								-DJSC_LIBRARY:FILEPATH=${JSC_LIBRARY}
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
						set_tests_properties("${TEST_NAME}" PROPERTIES DEPENDS uscxml-transform)
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
						set_tests_properties("${TEST_NAME}" PROPERTIES DEPENDS jar)
						set(TEST_ADDED ON)
					endif ()

					if (PYTHON_BIN AND TEST_LANG STREQUAL "python")
						add_test(NAME "${TEST_NAME}"
								COMMAND
								${PYTHON_BIN}
								${PROJECT_SOURCE_DIR}/contrib/python/bindings/test-state-pass.py
								${W3C_TEST}
								WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}/contrib/python/bindings)
						
						set_tests_properties("${TEST_NAME}" PROPERTIES ENVIRONMENT "USCXML_PYTHON_PATH=${CMAKE_LIBRARY_OUTPUT_DIRECTORY}")
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
					set_tests_properties("${TEST_NAME}" PROPERTIES PASS_REGULAR_EXPRESSION "depth reached [0-9]+, errors: 0")
					set_tests_properties("${TEST_NAME}" PROPERTIES FAIL_REGULAR_EXPRESSION "depth reached [0-9]+, errors: [1-9]+")
					set(TEST_ADDED ON)

				elseif (TEST_TYPE MATCHES "^fsm.*")

					add_test("${TEST_NAME}" ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-state-pass -f ${W3C_TEST})
					set(TEST_ADDED ON)

				endif ()

				if (TEST_ADDED)
					set_property(TEST ${TEST_NAME} PROPERTY LABELS ${TEST_NAME})
					set_tests_properties(${TEST_NAME} PROPERTIES TIMEOUT ${TEST_TIMEOUT})
					if (IS_PERFORMANCE_TEST)
						set_tests_properties("${TEST_NAME}" PROPERTIES ENVIRONMENT USCXML_BENCHMARK_ITERATIONS=${TEST_BENCHMARK_ITERATIONS})
					endif ()
				endif ()

			endif ()
		endforeach ()
	endforeach ()

endif ()