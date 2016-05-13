set(TEST_TIMEOUT 15)
set(TEST_BENCHMARK_ITERATIONS 1000)

find_program(SPIN spin)
find_program(CC gcc)
find_program(CXX g++)

function(USCXML_TEST_COMPILE)
	set(options BUILD_ONLY)
	set(oneValueArgs LABEL NAME)
	set(multiValueArgs FILES ARGS)
	cmake_parse_arguments(USCXML_TEST "${options}" "${oneValueArgs}" "${multiValueArgs}" ${ARGN})

	if (WIN32)
		list(APPEND USCXML_TEST_FILES "${PROJECT_SOURCE_DIR}/contrib/src/getopt/getopt.c")
	endif()

	add_executable(${USCXML_TEST_NAME} ${USCXML_TEST_FILES})
	target_link_libraries(${USCXML_TEST_NAME} uscxml)
	if (NOT ${USCXML_TEST_BUILD_ONLY})
		add_test(${USCXML_TEST_NAME} ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/${USCXML_TEST_NAME} ${USCXML_TEST_ARGS})
		set_property(TEST ${USCXML_TEST_NAME} PROPERTY LABELS ${USCXML_TEST_LABEL})
	endif()
	set_target_properties(${USCXML_TEST_NAME} PROPERTIES FOLDER "Tests")
endfunction()

# simple one file tests
USCXML_TEST_COMPILE(NAME test-url LABEL general/test-url FILES src/test-url.cpp)
USCXML_TEST_COMPILE(NAME test-lifecycle LABEL general/test-lifecycle FILES src/test-lifecycle.cpp)
USCXML_TEST_COMPILE(NAME test-validating LABEL general/test-validating FILES src/test-validating.cpp)

# the one binary to test for pass / fail final states
if (WIN32)
	add_executable(test-state-pass src/test-state-pass.cpp ${PROJECT_SOURCE_DIR}/contrib/src/getopt/getopt.c)
else()
	add_executable(test-state-pass src/test-state-pass.cpp)
endif()
target_link_libraries(test-state-pass uscxml)
set_target_properties(test-state-pass PROPERTIES FOLDER "Tests")

add_executable(test-gen-c src/test-gen-c.cpp)
target_link_libraries(test-gen-c uscxml)
set_target_properties(test-gen-c PROPERTIES FOLDER "Tests")

# issues
file(GLOB_RECURSE USCXML_ISSUES
	issues/*.cpp
	issues/*.scxml
)
foreach(USCXML_ISSUE ${USCXML_ISSUES} )
	get_filename_component(ISSUE_NAME ${USCXML_ISSUE} NAME_WE)
	get_filename_component(ISSUE_TYPE ${USCXML_ISSUE} EXT)
	if (ISSUE_TYPE STREQUAL ".scxml")
		add_test(issue/${ISSUE_NAME} ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-state-pass ${USCXML_ISSUE})
		set_property(TEST issue/${ISSUE_NAME} PROPERTY LABELS issue/${ISSUE_NAME})
	else()
		USCXML_TEST_COMPILE(NAME ${ISSUE_NAME} LABEL issues/${ISSUE_NAME} FILES ${USCXML_ISSUE})
	endif()
endforeach()

# make sure all headers are self-reliant
file(GLOB_RECURSE USCXML_HEADERS
	../src/*.h
	../src/*.hpp
)

foreach(USCXML_HEADER ${USCXML_HEADERS} )
	STRING(REGEX REPLACE "${CMAKE_CURRENT_SOURCE_DIR}/../src/" "" USCXML_REL_HEADER ${USCXML_HEADER})

	set(HEADER_TEST)
	set(HEADER_TEST "${HEADER_TEST}#include \"${USCXML_HEADER}\"\n")
	set(HEADER_TEST "${HEADER_TEST}int main(int argc, char** argv) {}")
	FILE(WRITE ${CMAKE_CURRENT_BINARY_DIR}/headers/${USCXML_REL_HEADER}.cpp ${HEADER_TEST})

	add_test(NAME "header/${USCXML_REL_HEADER}"
		COMMAND ${CMAKE_COMMAND}
			-DTESTFILE:FILEPATH=${CMAKE_CURRENT_BINARY_DIR}/headers/${USCXML_REL_HEADER}.cpp
			-DCC_BIN:FILEPATH=${CC}
			-DCXX_BIN:FILEPATH=${CXX}
			-DPROJECT_SOURCE_DIR=${PROJECT_SOURCE_DIR}
			-DUSCXML_PLATFORM_ID=${USCXML_PLATFORM_ID}
			-DCMAKE_BINARY_DIR=${CMAKE_BINARY_DIR}
			-DPROJECT_BINARY_DIR=${PROJECT_BINARY_DIR}
			-DCMAKE_LIBRARY_OUTPUT_DIRECTORY=${CMAKE_LIBRARY_OUTPUT_DIRECTORY}
		-P ${CMAKE_CURRENT_SOURCE_DIR}/ctest/scripts/run_header_compiles.cmake)
	set_property(TEST "header/${USCXML_REL_HEADER}" PROPERTY LABELS "header/${USCXML_REL_HEADER}")
	
endforeach()

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
		# "promela"

		# generated c source
		"gen/c/ecma"
		# "gen/c/xpath"
		"gen/c/lua"
		# "gen/c/promela"
		# "gen/vhdl/ecma"
		
		# state-machine interpreters
		# "fsm/ecma"
		# "fsm/xpath"
		# "fsm/lua"
		# "fsm/promela"

		# formal verification
		# "spin/promela"

		# performance tests
		# "perf/gen/c/ecma"
		# "perf/ecma"
	)

	# prepare directories for test classes and copy resources over
	foreach(W3C_RESOURCE ${W3C_RESOURCES} )
		get_filename_component(TEST_DATAMODEL ${W3C_RESOURCE} PATH)
		get_filename_component(TEST_DATAMODEL ${TEST_DATAMODEL} NAME)
		
		# message(STATUS "W3C_RESOURCE: ${W3C_RESOURCE}")
		# message(STATUS "TEST_DATAMODEL: ${TEST_DATAMODEL}")
		
		foreach(TEST_CLASS ${TEST_CLASSES})
			# datamodel has to be the suffix of the test class
			if (TEST_CLASS MATCHES ".*/${TEST_DATAMODEL}$")
				file(COPY ${W3C_RESOURCE} DESTINATION ${CMAKE_CURRENT_BINARY_DIR}/${TEST_CLASS})
			endif()
		endforeach()
	endforeach()

	# establish actual tests
	foreach(TEST_CLASS ${TEST_CLASSES})
		get_filename_component(TEST_DATAMODEL ${TEST_CLASS} NAME)
		get_filename_component(TEST_TYPE ${TEST_CLASS} PATH)

		# get all respective scxml files into W3C_TESTS
		file(GLOB_RECURSE W3C_TESTS w3c/${TEST_DATAMODEL}/*.scxml)
				
		SET(IS_PERFORMANCE_TEST OFF)
		if (TEST_CLASS MATCHES "^perf/.*")
			SET(IS_PERFORMANCE_TEST ON)
		endif()
		
		if (IS_PERFORMANCE_TEST)
			string(REGEX REPLACE "^perf/?" "" TEST_TYPE ${TEST_TYPE})
		endif()
		
		SET(IS_STANDARD_TEST OFF)
		if ("${TEST_TYPE}" STREQUAL "")
			if (IS_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/w3c/${TEST_DATAMODEL}")
				SET(IS_STANDARD_TEST ON)
			endif()
		endif()
		
		# normal IRP tests - get all scxml files within
		foreach(W3C_TEST ${W3C_TESTS} )
			get_filename_component(TEST_FILE ${W3C_TEST} NAME)
			set(TEST_NAME "w3c/${TEST_CLASS}/${TEST_FILE}")

			if (NOT TEST_NAME MATCHES ".*sub.*")
				if (IS_STANDARD_TEST)
					
					add_test(${TEST_NAME} ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-state-pass ${W3C_TEST})
			
					if (TEST_NAME MATCHES ".*/test250.scxml")
						set_tests_properties(${TEST_NAME} PROPERTIES FAIL_REGULAR_EXPRESSION "entering final state, invocation was not cancelled")
					elseif (TEST_NAME MATCHES ".*/test307.scxml")
						set_tests_properties(${TEST_NAME} PROPERTIES FAIL_REGULAR_EXPRESSION "error in state")
					endif()
			
					# more properties for standard tests
		
				else()

					if (TEST_TYPE MATCHES "^gen.*")
						get_filename_component(TEST_TARGET ${TEST_TYPE} NAME)
						if (TEST_TYPE MATCHES "^gen/${TEST_TARGET}")

							# generate native interpreters
							add_test(NAME "${TEST_NAME}"
								COMMAND ${CMAKE_COMMAND}
									-DOUTDIR:FILEPATH=${CMAKE_CURRENT_BINARY_DIR}/${TEST_CLASS}
									-DTESTFILE:FILEPATH=${W3C_TEST}
									-DTARGETLANG=${TEST_TARGET}
									-DJSC_LIBRARY:FILEPATH=${JSC_LIBRARY}
									-DUSCXML_TRANSFORM_BIN:FILEPATH=${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/uscxml-transform
									-DCC_BIN:FILEPATH=${CC}
									-DCXX_BIN:FILEPATH=${CXX}
									-DPROJECT_SOURCE_DIR=${PROJECT_SOURCE_DIR}
									-DUSCXML_PLATFORM_ID=${USCXML_PLATFORM_ID}
									-DCMAKE_BINARY_DIR=${CMAKE_BINARY_DIR}
									-DPROJECT_BINARY_DIR=${PROJECT_BINARY_DIR}
									-DXercesC_INCLUDE_DIRS=${XercesC_INCLUDE_DIRS}
									-DURIPARSER_INCLUDE_DIR=${URIPARSER_INCLUDE_DIR}
									-DLIBEVENT_INCLUDE_DIR=${LIBEVENT_INCLUDE_DIR}
									-DCMAKE_LIBRARY_OUTPUT_DIRECTORY=${CMAKE_LIBRARY_OUTPUT_DIRECTORY}
									-DSCAFFOLDING_FOR_GENERATED_C:FILEPATH=${CMAKE_CURRENT_SOURCE_DIR}/src/test-gen-c.cpp
									-P ${CMAKE_CURRENT_SOURCE_DIR}/ctest/scripts/run_generated_test.cmake)
							set_tests_properties("${TEST_NAME}" PROPERTIES DEPENDS uscxml-transform)

						endif()

					elseif (TEST_TYPE MATCHES "^spin.*")

						if (NOT ${TEST_DATAMODEL} STREQUAL "promela")
							break()
						endif()

						add_test(NAME "${TEST_NAME}"
							COMMAND ${CMAKE_COMMAND}
								-DOUTDIR:FILEPATH=${CMAKE_CURRENT_BINARY_DIR}/promela
								-DTESTFILE:FILEPATH=${W3C_TEST}
								-DUSCXML_TRANSFORM_BIN:FILEPATH=${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/uscxml-transform
								-DSPIN_BIN:FILEPATH=${SPIN}
								-DCC_BIN:FILEPATH=${CC}
								-P ${CMAKE_CURRENT_SOURCE_DIR}/ctest/scripts/run_promela_test.cmake)
						set_tests_properties("${TEST_NAME}" PROPERTIES PASS_REGULAR_EXPRESSION "depth reached [0-9]+, errors: 0")
						set_tests_properties("${TEST_NAME}" PROPERTIES FAIL_REGULAR_EXPRESSION "depth reached [0-9]+, errors: [1-9]+")
						
					elseif (TEST_TYPE MATCHES "^fsm.*")
							
						add_test("${TEST_NAME}" ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-state-pass -f ${W3C_TEST})
							
					endif()
				endif()
				
				set_property(TEST ${TEST_NAME} PROPERTY LABELS ${TEST_NAME})
				set_tests_properties(${TEST_NAME} PROPERTIES TIMEOUT ${TEST_TIMEOUT})
				if (IS_PERFORMANCE_TEST)
					set_tests_properties("${TEST_NAME}" PROPERTIES ENVIRONMENT USCXML_BENCHMARK_ITERATIONS=${TEST_BENCHMARK_ITERATIONS})
				endif()
				
			endif()
		endforeach()
	endforeach()

endif()