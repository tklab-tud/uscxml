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
	USCXML_TEST_COMPILE(BUILD_ONLY NAME test-stress LABEL general/test-stress FILES src/test-stress.cpp)
endif()

if (APPLE)
	USCXML_TEST_COMPILE(BUILD_ONLY NAME test-dirmon LABEL general/test-dirmon FILES src/test-dirmon.cpp)
endif()

USCXML_TEST_COMPILE(BUILD_ONLY NAME test-sockets LABEL general/test-sockets FILES src/test-sockets.cpp)

USCXML_TEST_COMPILE(NAME test-url LABEL general/test-url FILES src/test-url.cpp)
USCXML_TEST_COMPILE(NAME test-base64 LABEL general/test-base64 FILES src/test-base64.cpp)
USCXML_TEST_COMPILE(NAME test-eventdelay LABEL general/test-eventdelay FILES src/test-eventdelay.cpp)
USCXML_TEST_COMPILE(NAME test-flat-stateid LABEL general/test-flat-stateid FILES src/test-flat-stateid.cpp)
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


if (NOT BUILD_MINIMAL)
	add_executable(test-w3c src/test-w3c.cpp)
	target_link_libraries(test-w3c uscxml)
	set_target_properties(test-w3c PROPERTIES FOLDER "Tests")

	file(GLOB_RECURSE W3C_TESTS
		w3c/*.scxml
	)

	foreach( W3C_TEST ${W3C_TESTS} )
		string(REGEX MATCH "[^//]+/[^//]+.scxml" TEST_NAME ${W3C_TEST})
	#	message("TEST_NAME: ${TEST_NAME}")
		if (NOT TEST_NAME MATCHES ".*sub.*")
			if (BUILD_TESTS_W3C_ECMA AND TEST_NAME MATCHES "^ecma\\/.*")
				add_test(${TEST_NAME} ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-w3c ${W3C_TEST})
				set_property(TEST ${TEST_NAME} PROPERTY LABELS ${TEST_NAME})
	#			set_tests_properties(${TEST_NAME} PROPERTIES FAIL_REGULAR_EXPRESSION "TEST FAILED")
				if (TEST_NAME STREQUAL "ecma/test250.scxml")
					set_tests_properties(${TEST_NAME} PROPERTIES 
						FAIL_REGULAR_EXPRESSION "entering final state, invocation was not cancelled")
				elseif (TEST_NAME STREQUAL "ecma/test307.scxml")
					set_tests_properties(${TEST_NAME} PROPERTIES
						FAIL_REGULAR_EXPRESSION "error in state")
				endif()
			endif()
		
			if (BUILD_TESTS_FSM_ECMA AND TEST_NAME MATCHES "^ecma\\/.*")
				add_test("fsm/${TEST_NAME}" ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-w3c -f ${W3C_TEST})
				set_property(TEST "fsm/${TEST_NAME}" PROPERTY LABELS "fsm/${TEST_NAME}")
			endif()
		
			if (BUILD_TESTS_W3C_XPATH AND TEST_NAME MATCHES "^xpath\\/.*")
				add_test(${TEST_NAME} ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-w3c ${W3C_TEST})
				set_property(TEST ${TEST_NAME} PROPERTY LABELS ${TEST_NAME})
	#			set_tests_properties(${TEST_NAME} PROPERTIES FAIL_REGULAR_EXPRESSION "TEST FAILED")
			endif()
		
			if (BUILD_TESTS_FSM_XPATH AND TEST_NAME MATCHES "^xpath\\/.*")
				add_test("fsm/${TEST_NAME}" ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-w3c -f ${W3C_TEST})
				set_property(TEST "fsm/${TEST_NAME}" PROPERTY LABELS "fsm/${TEST_NAME}")
			endif()

			if (BUILD_DM_LUA AND LUA_FOUND AND BUILD_TESTS_W3C_LUA AND TEST_NAME MATCHES "^lua\\/.*")
				add_test(${TEST_NAME} ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-w3c ${W3C_TEST})
				set_property(TEST ${TEST_NAME} PROPERTY LABELS ${TEST_NAME})
	#			set_tests_properties(${TEST_NAME} PROPERTIES FAIL_REGULAR_EXPRESSION "TEST FAILED")
			endif()
		
		endif()
	endforeach()
endif()