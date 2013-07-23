# find_program(XMLLINT xmllint)
# if (XMLLINT)
# 	file(GLOB SCXML_FILES samples/uscxml/*.scxml)
# endif()

if (NOT WIN32)
	add_executable(test-predicates src/test-predicates.cpp)
	target_link_libraries(test-predicates uscxml)
	add_test(test-predicates ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-predicates ${CMAKE_SOURCE_DIR}/test/samples/uscxml/test-predicates.scxml)
	set_target_properties(test-predicates PROPERTIES FOLDER "Tests")
endif()

add_test(test-execution ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/uscxml-browser ${CMAKE_SOURCE_DIR}/test/samples/uscxml/test-execution.scxml)
add_test(test-communication ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/uscxml-browser ${CMAKE_SOURCE_DIR}/test/samples/uscxml/test-communication.scxml)
add_test(test-done-data ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/uscxml-browser ${CMAKE_SOURCE_DIR}/test/samples/uscxml/test-donedata.scxml)

if (SWI_FOUND)
	add_test(test-prolog-swi ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/uscxml-browser ${CMAKE_SOURCE_DIR}/test/samples/uscxml/test-prolog.scxml)
endif()

if (V8_FOUND)
	add_test(test-ecmascript ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/uscxml-browser ${CMAKE_SOURCE_DIR}/test/samples/uscxml/test-ecmascript.scxml)
endif()

if (OPENSCENEGRAPH_FOUND AND OFF)
	add_executable(test-osg src/test-osg.cpp)
	target_link_libraries(test-osg uscxml)
	set_target_properties(test-osg PROPERTIES FOLDER "Tests")
endif()

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

if (NOT WIN32)
	add_executable(test-arabica-events src/test-arabica-events.cpp)
	target_link_libraries(test-arabica-events uscxml)
	add_test(test-arabica-events ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-arabica-events ${CMAKE_SOURCE_DIR}/test/samples/uscxml/arabica/test-arabica-events.xml)
	set_target_properties(test-arabica-events PROPERTIES FOLDER "Tests")

	add_executable(test-arabica-xpath src/test-arabica-xpath.cpp)
	target_link_libraries(test-arabica-xpath uscxml)
	add_test(test-arabica-xpath ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-arabica-xpath)
	set_target_properties(test-arabica-xpath PROPERTIES FOLDER "Tests")

	add_executable(test-arabica-parsing src/test-arabica-parsing.cpp)
	target_link_libraries(test-arabica-parsing uscxml)
	add_test(test-arabica-xpath ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-arabica-parsing)
	set_target_properties(test-arabica-parsing PROPERTIES FOLDER "Tests")

endif()

add_executable(test-url src/test-url.cpp)
target_link_libraries(test-url uscxml)
add_test(test-url ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-url)
set_target_properties(test-url PROPERTIES FOLDER "Tests")

# add_executable(test-initial-config src/test-initial-config.cpp)
# target_link_libraries(test-initial-config uscxml)
# add_test(test-url ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-initial-config ${CMAKE_SOURCE_DIR}/test/samples/uscxml/test-initial-config.scxml)
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

add_executable(scxml-test-framework-client 
	src/scxml-test-framework-client.cpp)
	target_link_libraries(scxml-test-framework-client uscxml)
set_target_properties(scxml-test-framework-client PROPERTIES FOLDER "Tests")

# add_executable(test-curl-multi-api src/test-curl-multi-api.cpp)
# target_link_libraries(test-curl-multi-api uscxml)
# add_test(test-curl-multi-api ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-completion)
# set_target_properties(test-curl-multi-api PROPERTIES FOLDER "Tests")

	add_executable(test-w3c src/test-w3c.cpp ${PROJECT_SOURCE_DIR}/contrib/src/getopt/XGetopt.cpp)
	target_link_libraries(test-w3c uscxml)
	set_target_properties(test-w3c PROPERTIES FOLDER "Tests")

file(GLOB_RECURSE W3C_TESTS
	samples/w3c/*.scxml
)

foreach( W3C_TEST ${W3C_TESTS} )
	string(REGEX MATCH "[^//]+/[^//]+.scxml" TEST_NAME ${W3C_TEST})
	#message("TEST_NAME: ${TEST_NAME}")
	if (NOT TEST_NAME MATCHES ".*sub.*")
		if (RUN_W3C_ECMA_TESTS AND TEST_NAME MATCHES "^ecma\\/.*")
			add_test(${TEST_NAME} ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-w3c ${W3C_TEST})
		endif()
		if (RUN_W3C_XPATH_TESTS AND TEST_NAME MATCHES "^xpath\\/.*")
			add_test(${TEST_NAME} ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-w3c ${W3C_TEST})
		endif()
	endif()
endforeach()
