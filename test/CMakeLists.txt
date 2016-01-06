set(TEST_TIMEOUT 10)

function(USCXML_TEST_COMPILE)
	set(options BUILD_ONLY)
	set(oneValueArgs LABEL NAME)
	set(multiValueArgs FILES ARGS)
	cmake_parse_arguments(USCXML_TEST "${options}" "${oneValueArgs}" "${multiValueArgs}" ${ARGN})

	add_executable(${USCXML_TEST_NAME} ${USCXML_TEST_FILES})
	target_link_libraries(${USCXML_TEST_NAME} uscxml)
	if (NOT ${USCXML_TEST_BUILD_ONLY})
		add_test(${USCXML_TEST_NAME} ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/${USCXML_TEST_NAME} ${USCXML_TEST_ARGS})
		set_property(TEST ${USCXML_TEST_NAME} PROPERTY LABELS ${USCXML_TEST_LABEL})
	endif()
	set_target_properties(${USCXML_TEST_NAME} PROPERTIES FOLDER "Tests")
endfunction()

if (NOT WIN32)
	USCXML_TEST_COMPILE(NAME test-predicates LABEL general/test-predicates FILES src/test-predicates.cpp)	
	USCXML_TEST_COMPILE(BUILD_ONLY NAME test-vxml-mmi-socket LABEL general/test-vxml-mmi-socket FILES src/test-vxml-mmi-socket.cpp)
	USCXML_TEST_COMPILE(BUILD_ONLY NAME test-vxml-mmi-http LABEL general/test-vxml-mmi-http FILES src/test-vxml-mmi-http.cpp)
	USCXML_TEST_COMPILE(BUILD_ONLY NAME test-arabica-xpath LABEL general/test-arabica-xpath FILES src/test-arabica-xpath.cpp)
	USCXML_TEST_COMPILE(NAME test-mmi LABEL general/test-mmi FILES src/test-mmi.cpp)
	USCXML_TEST_COMPILE(NAME test-trie LABEL general/test-trie FILES src/test-trie.cpp)
	USCXML_TEST_COMPILE(NAME test-arabica-namespaces LABEL general/test-arabica-namespaces FILES src/test-arabica-namespaces.cpp)
	USCXML_TEST_COMPILE(NAME test-arabica-events LABEL general/test-arabica-events FILES src/test-arabica-events.cpp
		ARGS ${CMAKE_CURRENT_SOURCE_DIR}/uscxml/arabica/test-arabica-events.xml)
	USCXML_TEST_COMPILE(NAME test-arabica-parsing LABEL general/test-arabica-parsing FILES src/test-arabica-parsing.cpp)
	USCXML_TEST_COMPILE(NAME test-promela-parser LABEL general/test-promela-parser FILES src/test-promela-parser.cpp)
	target_link_libraries(test-promela-parser uscxml_transform)
	USCXML_TEST_COMPILE(BUILD_ONLY NAME test-stress LABEL general/test-stress FILES src/test-stress.cpp)

	USCXML_TEST_COMPILE(NAME test-c-machine LABEL general/test-c-machine FILES src/test-c-machine.cpp)
	USCXML_TEST_COMPILE(NAME test-misc LABEL general/test-misc FILES src/test-misc.cpp)

endif()

if (APPLE)
	USCXML_TEST_COMPILE(BUILD_ONLY NAME test-dirmon LABEL general/test-dirmon FILES src/test-dirmon.cpp)
endif()

USCXML_TEST_COMPILE(BUILD_ONLY NAME test-sockets LABEL general/test-sockets FILES src/test-sockets.cpp)

USCXML_TEST_COMPILE(NAME test-url LABEL general/test-url FILES src/test-url.cpp)
USCXML_TEST_COMPILE(NAME test-doneevent LABEL general/test-doneevent FILES src/test-doneevent.cpp)
USCXML_TEST_COMPILE(NAME test-base64 LABEL general/test-base64 FILES src/test-base64.cpp)
USCXML_TEST_COMPILE(NAME test-eventdelay LABEL general/test-eventdelay FILES src/test-eventdelay.cpp)
USCXML_TEST_COMPILE(NAME test-flat-stateid LABEL general/test-flat-stateid FILES src/test-flat-stateid.cpp)
target_link_libraries(test-flat-stateid uscxml_transform)
USCXML_TEST_COMPILE(NAME test-lifecycle LABEL general/test-lifecycle FILES src/test-lifecycle.cpp)
USCXML_TEST_COMPILE(NAME test-issue-reporting LABEL general/test-issue-reporting FILES src/test-issue-reporting.cpp)
USCXML_TEST_COMPILE(NAME test-cmdline-parsing LABEL general/test-cmdline-parsing FILES src/test-cmdline-parsing.cpp)
USCXML_TEST_COMPILE(NAME test-datamodel LABEL general/test-datamodel FILES src/test-datamodel.cpp)


if (EXPECT_FOUND AND TCL_FOUND)
	USCXML_TEST_COMPILE(BUILD_ONLY NAME test-expect LABEL general/test-expect FILES src/test-expect.cpp)
endif()

if (LIBPURPLE_FOUND)
	USCXML_TEST_COMPILE(BUILD_ONLY NAME test-instant-messaging LABEL general/test-instant-messaging FILES src/test-instant-messaging.cpp)
endif()

if (FFMPEG_FOUND)
	USCXML_TEST_COMPILE(BUILD_ONLY NAME test-ffmpeg LABEL general/test-ffmpeg FILES src/test-ffmpeg.cpp)
endif()

if (SWI_FOUND)
	add_test(test-prolog-swi ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/uscxml-browser -t2345 ${CMAKE_SOURCE_DIR}/test/uscxml/test-prolog.scxml)
endif()

if (ECMA_FOUND)
	add_test(test-ecmascript ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/uscxml-browser ${CMAKE_SOURCE_DIR}/test/uscxml/test-ecmascript.scxml)
endif()

add_test(test-execution ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/uscxml-browser ${CMAKE_SOURCE_DIR}/test/uscxml/test-execution.scxml)
add_test(test-communication ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/uscxml-browser -t5493 ${CMAKE_SOURCE_DIR}/test/uscxml/test-communication.scxml)
add_test(test-done-data ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/uscxml-browser ${CMAKE_SOURCE_DIR}/test/uscxml/test-donedata.scxml)

find_program(SPIN spin)
find_program(GCC gcc)
find_program(GPP g++)

if (NOT BUILD_MINIMAL)
	# compile and add all reported issues tests
	
	add_executable(test-w3c src/test-w3c.cpp)
	target_link_libraries(test-w3c uscxml uscxml_transform)
	set_target_properties(test-w3c PROPERTIES FOLDER "Tests")

	# copy resources
	file(GLOB_RECURSE W3C_RESOURCES
		w3c/*.txt
		w3c/*sub*.scxml
	)

	foreach(W3C_RESOURCE ${W3C_RESOURCES} )
		# we abuse this as head and tail
		get_filename_component(W3C_RESOURCE_PATH ${W3C_RESOURCE} PATH)
		get_filename_component(W3C_TEST_TYPE ${W3C_RESOURCE_PATH} NAME)
		
		if (BUILD_TESTS_W3C_ECMA AND W3C_TEST_TYPE STREQUAL "ecma")
			file(COPY ${W3C_RESOURCE} DESTINATION ${CMAKE_CURRENT_BINARY_DIR}/ecma)
		elseif (BUILD_TESTS_W3C_XPATH AND W3C_TEST_TYPE STREQUAL "xpath")
			file(COPY ${W3C_RESOURCE} DESTINATION ${CMAKE_CURRENT_BINARY_DIR}/xpath)
		elseif (BUILD_TESTS_W3C_LUA AND W3C_TEST_TYPE STREQUAL "lua")
			file(COPY ${W3C_RESOURCE} DESTINATION ${CMAKE_CURRENT_BINARY_DIR}/lua)
		elseif (BUILD_TESTS_W3C_PROMELA AND W3C_TEST_TYPE STREQUAL "promela")
			file(COPY ${W3C_RESOURCE} DESTINATION ${CMAKE_CURRENT_BINARY_DIR}/lua)
		endif()
		
	endforeach()

	# prepare tests
	file(GLOB_RECURSE W3C_TESTS
		w3c/*.scxml
	)

	foreach( W3C_TEST ${W3C_TESTS} )
		string(REGEX MATCH "[^//]+/[^//]+.scxml" TEST_NAME ${W3C_TEST})
	#	message("TEST_NAME: ${TEST_NAME}")
		if (NOT TEST_NAME MATCHES ".*sub.*")
			if (TEST_NAME MATCHES "^null\\/.*")
				add_test(${TEST_NAME} ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-w3c ${W3C_TEST})
				set_property(TEST ${TEST_NAME} PROPERTY LABELS ${TEST_NAME})
				set_tests_properties(${TEST_NAME} PROPERTIES TIMEOUT ${TEST_TIMEOUT})
			endif()

			if (BUILD_TESTS_W3C_ECMA AND TEST_NAME MATCHES "^ecma\\/.*")
				add_test(${TEST_NAME} ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-w3c ${W3C_TEST})
				set_property(TEST ${TEST_NAME} PROPERTY LABELS ${TEST_NAME})
				set_tests_properties(${TEST_NAME} PROPERTIES TIMEOUT ${TEST_TIMEOUT})
				
	#			set_tests_properties(${TEST_NAME} PROPERTIES FAIL_REGULAR_EXPRESSION "TEST FAILED")
	
				if (TEST_NAME STREQUAL "ecma/test250.scxml")
					set_tests_properties(${TEST_NAME} PROPERTIES 
						FAIL_REGULAR_EXPRESSION "entering final state, invocation was not cancelled")
				elseif (TEST_NAME STREQUAL "ecma/test307.scxml")
					set_tests_properties(${TEST_NAME} PROPERTIES
						FAIL_REGULAR_EXPRESSION "error in state")
				endif()
			endif()
		
			if (BUILD_TESTS_GENERATED_C AND TEST_NAME MATCHES "^ecma\\/.*")
				add_test(NAME "gen_c/${TEST_NAME}"
				    COMMAND ${CMAKE_COMMAND}
							-DOUTDIR:FILEPATH=${CMAKE_CURRENT_BINARY_DIR}/gen_c
							-DTESTFILE:FILEPATH=${W3C_TEST}
							-DJSC_LIBRARY:FILEPATH=${JSC_LIBRARY}
							-DUSCXML_TRANSFORM_BIN:FILEPATH=${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/uscxml-transform
							-DGCC_BIN:FILEPATH=${GCC}
							-DGPP_BIN:FILEPATH=${GPP}
							-DPROJECT_SOURCE_DIR=${PROJECT_SOURCE_DIR}
							-DUSCXML_PLATFORM_ID=${USCXML_PLATFORM_ID}
							-DCMAKE_BINARY_DIR=${CMAKE_BINARY_DIR}
							-DCMAKE_LIBRARY_OUTPUT_DIRECTORY=${CMAKE_LIBRARY_OUTPUT_DIRECTORY}
							-DSCAFFOLDING_FOR_GENERATED_C:FILEPATH=${CMAKE_CURRENT_SOURCE_DIR}/src/test-c-machine.cpp
							-P ${CMAKE_CURRENT_SOURCE_DIR}/w3c/run_generated_c_test.cmake)
				set_property(TEST "gen_c/${TEST_NAME}" PROPERTY LABELS "gen_c/${TEST_NAME}")
				set_tests_properties("gen_c/${TEST_NAME}" PROPERTIES TIMEOUT ${TEST_TIMEOUT})
				set_tests_properties("gen_c/${TEST_NAME}" PROPERTIES DEPENDS uscxml-transform)
				
			endif()
			
			if (BUILD_TESTS_FSM AND BUILD_TESTS_FSM_ECMA AND TEST_NAME MATCHES "^ecma\\/.*")
				add_test("fsm/${TEST_NAME}" ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-w3c -f ${W3C_TEST})
				set_property(TEST "fsm/${TEST_NAME}" PROPERTY LABELS "fsm/${TEST_NAME}")
				set_tests_properties("fsm/${TEST_NAME}" PROPERTIES TIMEOUT ${TEST_TIMEOUT})

				add_test(NAME "minimized/${TEST_NAME}"
				    COMMAND ${CMAKE_COMMAND}
							-DOUTDIR:FILEPATH=${CMAKE_CURRENT_BINARY_DIR}/ecma
							-DTESTFILE:FILEPATH=${W3C_TEST}
							-DUSCXML_TRANSFORM_BIN:FILEPATH=${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/uscxml-transform
							-DUSCXML_W3C_TEST_BIN:FILEPATH=${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-w3c
						-P ${CMAKE_CURRENT_SOURCE_DIR}/w3c/run_minimized_test.cmake)
				set_property(TEST "minimized/${TEST_NAME}" PROPERTY LABELS "minimized/${TEST_NAME}")
				set_tests_properties("minimized/${TEST_NAME}" PROPERTIES TIMEOUT ${TEST_TIMEOUT})

				set_tests_properties(${TEST_NAME} PROPERTIES DEPENDS uscxml-transform)
				set_tests_properties(${TEST_NAME} PROPERTIES DEPENDS test-w3c)

				# add_test(NAME "fsm/minimized/${TEST_NAME}"
				#     COMMAND ${CMAKE_COMMAND}
				# 			-DOUTDIR:FILEPATH=${CMAKE_CURRENT_BINARY_DIR}/ecma
				# 			-DTESTFILE:FILEPATH=${W3C_TEST}
				# 			-DUSCXML_TRANSFORM_BIN:FILEPATH=${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/uscxml-transform
				# 			-DUSCXML_W3C_TEST_BIN:FILEPATH=${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-w3c
				# 		-P ${CMAKE_CURRENT_SOURCE_DIR}/w3c/run_minimized_flat_test.cmake)
				# set_property(TEST "fsm/minimized/${TEST_NAME}" PROPERTY LABELS "fsm/minimized/${TEST_NAME}")
				# set_tests_properties("fsm/minimized/${TEST_NAME}" PROPERTIES TIMEOUT ${TEST_TIMEOUT})

				# set_tests_properties(${TEST_NAME} PROPERTIES DEPENDS uscxml-transform)
				# set_tests_properties(${TEST_NAME} PROPERTIES DEPENDS test-w3c)

			endif()
		
			if (BUILD_TESTS_W3C_XPATH AND TEST_NAME MATCHES "^xpath\\/.*")
				add_test(${TEST_NAME} ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-w3c ${W3C_TEST})
				set_property(TEST ${TEST_NAME} PROPERTY LABELS ${TEST_NAME})
				set_tests_properties(${TEST_NAME} PROPERTIES TIMEOUT ${TEST_TIMEOUT})
	#			set_tests_properties(${TEST_NAME} PROPERTIES FAIL_REGULAR_EXPRESSION "TEST FAILED")
				if (BUILD_TESTS_FSM AND BUILD_TESTS_FSM_XPATH)
					add_test("fsm/${TEST_NAME}" ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-w3c -f ${W3C_TEST})
					set_property(TEST "fsm/${TEST_NAME}" PROPERTY LABELS "fsm/${TEST_NAME}")
					set_tests_properties("fsm/${TEST_NAME}" PROPERTIES TIMEOUT ${TEST_TIMEOUT})
				endif()
			endif()
		
			if (BUILD_DM_LUA AND LUA_FOUND AND BUILD_TESTS_W3C_LUA AND TEST_NAME MATCHES "^lua\\/.*")
				add_test(${TEST_NAME} ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-w3c ${W3C_TEST})
				set_property(TEST ${TEST_NAME} PROPERTY LABELS ${TEST_NAME})
				set_tests_properties(${TEST_NAME} PROPERTIES TIMEOUT ${TEST_TIMEOUT})
	#			set_tests_properties(${TEST_NAME} PROPERTIES FAIL_REGULAR_EXPRESSION "TEST FAILED")
				if (BUILD_TESTS_FSM AND BUILD_TESTS_FSM_LUA)
					add_test("fsm/${TEST_NAME}" ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-w3c -f ${W3C_TEST})
					set_property(TEST "fsm/${TEST_NAME}" PROPERTY LABELS "fsm/${TEST_NAME}")
					set_tests_properties("fsm/${TEST_NAME}" PROPERTIES TIMEOUT ${TEST_TIMEOUT})
				endif()
	
			endif()

			if (BUILD_DM_PROLOG AND SWI_FOUND AND BUILD_TESTS_W3C_PROLOG AND TEST_NAME MATCHES "^prolog\\/.*")
				add_test(${TEST_NAME} ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-w3c ${W3C_TEST})
				set_property(TEST ${TEST_NAME} PROPERTY LABELS ${TEST_NAME})
				set_tests_properties(${TEST_NAME} PROPERTIES TIMEOUT ${TEST_TIMEOUT})
	#			set_tests_properties(${TEST_NAME} PROPERTIES FAIL_REGULAR_EXPRESSION "TEST FAILED")
				if (BUILD_TESTS_FSM AND BUILD_TESTS_FSM_PROLOG)
					add_test("fsm/${TEST_NAME}" ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-w3c -f ${W3C_TEST})
					set_property(TEST "fsm/${TEST_NAME}" PROPERTY LABELS "fsm/${TEST_NAME}")
					set_tests_properties("fsm/${TEST_NAME}" PROPERTIES TIMEOUT ${TEST_TIMEOUT})
				endif()
			endif()
		
			if (BUILD_DM_PROMELA AND BUILD_TESTS_W3C_PROMELA AND TEST_NAME MATCHES "^promela\\/.*")
				add_test(${TEST_NAME} ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-w3c ${W3C_TEST})
				set_property(TEST ${TEST_NAME} PROPERTY LABELS ${TEST_NAME})
				set_tests_properties(${TEST_NAME} PROPERTIES TIMEOUT ${TEST_TIMEOUT})
	#			set_tests_properties(${TEST_NAME} PROPERTIES FAIL_REGULAR_EXPRESSION "TEST FAILED")
				if (BUILD_TESTS_FSM AND BUILD_TESTS_FSM_PROMELA)
					add_test("fsm/${TEST_NAME}" ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-w3c -f ${W3C_TEST})
					set_property(TEST "fsm/${TEST_NAME}" PROPERTY LABELS "fsm/${TEST_NAME}")
					set_tests_properties("fsm/${TEST_NAME}" PROPERTIES TIMEOUT ${TEST_TIMEOUT})
				endif()
			endif()
		
			if (GCC AND SPIN AND BUILD_DM_PROMELA AND BUILD_TESTS_W3C_PROMELA AND TEST_NAME MATCHES "^promela\\/.*")

				add_test(NAME "spin/${TEST_NAME}"
				    COMMAND ${CMAKE_COMMAND}
							-DOUTDIR:FILEPATH=${CMAKE_CURRENT_BINARY_DIR}/promela
							-DTESTFILE:FILEPATH=${W3C_TEST}
							-DUSCXML_TRANSFORM_BIN:FILEPATH=${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/uscxml-transform
							-DSPIN_BIN:FILEPATH=${SPIN}
							-DGCC_BIN:FILEPATH=${GCC}
							-P ${CMAKE_CURRENT_SOURCE_DIR}/w3c/run_promela_test.cmake)
				set_property(TEST "spin/${TEST_NAME}" PROPERTY LABELS "spin/${TEST_NAME}")
				set_tests_properties("spin/${TEST_NAME}" PROPERTIES TIMEOUT ${TEST_TIMEOUT})
				set_tests_properties("spin/${TEST_NAME}" PROPERTIES PASS_REGULAR_EXPRESSION "depth reached [0-9]+, errors: 0")
				set_tests_properties("spin/${TEST_NAME}" PROPERTIES FAIL_REGULAR_EXPRESSION "depth reached [0-9]+, errors: [1-9]+")

				set_tests_properties(${TEST_NAME} PROPERTIES DEPENDS uscxml-transform)
	#			set_tests_properties(${TEST_NAME} PROPERTIES FAIL_REGULAR_EXPRESSION "TEST FAILED")
			endif()
		
		endif()
	endforeach()
endif()