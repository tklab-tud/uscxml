# find_program(XMLLINT xmllint)
# if (XMLLINT)
# 	file(GLOB SCXML_FILES uscxml/*.scxml)
# endif()

if (NOT WIN32)
	add_executable(test-predicates src/test-predicates.cpp)
	target_link_libraries(test-predicates uscxml)
	add_test(test-predicates ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-predicates ${CMAKE_SOURCE_DIR}/test/uscxml/test-predicates.scxml)
	set_target_properties(test-predicates PROPERTIES FOLDER "Tests")
endif()

add_test(test-execution ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/uscxml-browser ${CMAKE_SOURCE_DIR}/test/uscxml/test-execution.scxml)
add_test(test-communication ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/uscxml-browser -t5493 ${CMAKE_SOURCE_DIR}/test/uscxml/test-communication.scxml)
add_test(test-done-data ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/uscxml-browser ${CMAKE_SOURCE_DIR}/test/uscxml/test-donedata.scxml)

if (SWI_FOUND)
	add_test(test-prolog-swi ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/uscxml-browser -t2345 ${CMAKE_SOURCE_DIR}/test/uscxml/test-prolog.scxml)
endif()

# if (FFMPEG_FOUND)
# 	add_executable(test-ffmpeg src/test-ffmpeg.cpp)
# 	target_link_libraries(test-ffmpeg uscxml)
# 	add_test(test-ffmpeg ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-ffmpeg)
# 	set_target_properties(test-ffmpeg PROPERTIES FOLDER "Tests")
# endif()

if (V8_FOUND)
	add_test(test-ecmascript ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/uscxml-browser ${CMAKE_SOURCE_DIR}/test/uscxml/test-ecmascript.scxml)
endif()

if (OPENSCENEGRAPH_FOUND AND OFF)
	add_executable(test-osg src/test-osg.cpp)
	target_link_libraries(test-osg uscxml)
	set_target_properties(test-osg PROPERTIES FOLDER "Tests")
endif()

add_executable(test-base64 src/test-base64.cpp)
target_link_libraries(test-base64 uscxml)
add_test(test-base64 ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-base64)
set_target_properties(test-base64 PROPERTIES FOLDER "Tests")

add_executable(test-trie src/test-trie.cpp)
target_link_libraries(test-trie uscxml)
add_test(test-trie ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-trie)
set_target_properties(test-trie PROPERTIES FOLDER "Tests")

add_executable(test-eventdelay src/test-eventdelay.cpp)
target_link_libraries(test-eventdelay uscxml)
add_test(test-eventdelay ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-eventdelay)
set_target_properties(test-eventdelay PROPERTIES FOLDER "Tests")

if (OFF)
	add_executable(test-dirmon src/test-dirmon.cpp)
	target_link_libraries(test-dirmon uscxml)
	add_test(test-dirmon ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-dirmon)
	set_target_properties(test-dirmon PROPERTIES FOLDER "Tests")
endif()

add_executable(test-lifecycle src/test-lifecycle.cpp)
target_link_libraries(test-lifecycle uscxml)
add_test(test-lifecycle ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-arabica-namespaces)
set_target_properties(test-lifecycle PROPERTIES FOLDER "Tests")

if (NOT WIN32)
	add_executable(test-arabica-namespaces src/test-arabica-namespaces.cpp)
	target_link_libraries(test-arabica-namespaces uscxml)
	add_test(test-arabica-namespaces ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-arabica-namespaces ${CMAKE_SOURCE_DIR}/test)
	set_target_properties(test-arabica-namespaces PROPERTIES FOLDER "Tests")
	
	add_executable(test-arabica-events src/test-arabica-events.cpp)
	target_link_libraries(test-arabica-events uscxml)
	add_test(test-arabica-events ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-arabica-events ${CMAKE_SOURCE_DIR}/test/uscxml/arabica/test-arabica-events.xml)
	set_target_properties(test-arabica-events PROPERTIES FOLDER "Tests")

	add_executable(test-arabica-xpath src/test-arabica-xpath.cpp)
	target_link_libraries(test-arabica-xpath uscxml)
	add_test(test-arabica-xpath ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-arabica-xpath)
	set_target_properties(test-arabica-xpath PROPERTIES FOLDER "Tests")

	add_executable(test-arabica-parsing src/test-arabica-parsing.cpp)
	target_link_libraries(test-arabica-parsing uscxml)
	add_test(test-arabica-xpath ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-arabica-parsing)
	set_target_properties(test-arabica-parsing PROPERTIES FOLDER "Tests")

	add_executable(test-stress src/test-stress.cpp)
	if (BUILD_AS_PLUGINS)
		target_link_libraries(test-stress uscxml invoker_dirmon)
	else()
		target_link_libraries(test-stress uscxml)
	endif()
	# add_test(test-stress ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-stress ${CMAKE_SOURCE_DIR}/test/w3c)
	set_target_properties(test-stress PROPERTIES FOLDER "Tests")

	# if (LIBPURPLE_FOUND)
	# 	add_executable(test-instant-messaging src/test-instant-messaging.cpp)
	# 	target_link_libraries(test-instant-messaging uscxml ${LIBPURPLE_LIBRARY} ${GLIB2_LIBRARIES} ${ICONV_LIBRARIES})
	# 	add_test(test-instant-messaging ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-instant-messaging)
	# 	set_target_properties(test-instant-messaging PROPERTIES FOLDER "Tests")
	# endif()
endif()

add_executable(test-url src/test-url.cpp)
target_link_libraries(test-url uscxml)
add_test(test-url ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-url)
set_target_properties(test-url PROPERTIES FOLDER "Tests")

add_executable(test-promela-parser src/test-promela-parser.cpp)
target_link_libraries(test-promela-parser uscxml)
add_test(test-url ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-promela-parser)
set_target_properties(test-promela-parser PROPERTIES FOLDER "Tests")

add_executable(test-cmdline-parsing src/test-cmdline-parsing.cpp)
target_link_libraries(test-cmdline-parsing uscxml)
add_test(test-cmdline-parsing ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-cmdline-parsing)
set_target_properties(test-cmdline-parsing PROPERTIES FOLDER "Tests")

# add_executable(test-initial-config src/test-initial-config.cpp)
# target_link_libraries(test-initial-config uscxml)
# add_test(test-url ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-initial-config ${CMAKE_SOURCE_DIR}/test/uscxml/test-initial-config.scxml)
# set_target_properties(test-initial-config PROPERTIES FOLDER "Tests")

add_executable(test-datamodel src/test-datamodel.cpp)
target_link_libraries(test-datamodel uscxml)
add_test(test-datamodel ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-datamodel)
set_target_properties(test-datamodel PROPERTIES FOLDER "Tests")

# if (NOT WIN32)
# 	add_executable(test-mmi src/test-mmi.cpp)
# 	target_link_libraries(test-mmi uscxml)
# 	add_test(test-url ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-mmi)
# 	set_target_properties(test-mmi PROPERTIES FOLDER "Tests")
# endif()

# add_executable(test-curl-multi-api src/test-curl-multi-api.cpp)
# target_link_libraries(test-curl-multi-api uscxml)
# add_test(test-curl-multi-api ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-completion)
# set_target_properties(test-curl-multi-api PROPERTIES FOLDER "Tests")

if (EXPECT_FOUND AND TCL_FOUND)
	add_executable(test-expect 
		src/test-expect.cpp)
		target_link_libraries(test-expect uscxml ${EXPECT_LIBRARY} ${TCL_LIBRARY})
	set_target_properties(test-expect PROPERTIES FOLDER "Tests")
endif()

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
		
	endif()
endforeach()
