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

add_test(test-execution ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/mmi-browser ${CMAKE_SOURCE_DIR}/test/samples/uscxml/test-execution.scxml)
add_test(test-communication ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/mmi-browser ${CMAKE_SOURCE_DIR}/test/samples/uscxml/test-communication.scxml)
add_test(test-done-data ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/mmi-browser ${CMAKE_SOURCE_DIR}/test/samples/uscxml/test-donedata.scxml)

if (SWI_FOUND)
	add_test(test-prolog-swi ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/mmi-browser ${CMAKE_SOURCE_DIR}/test/samples/uscxml/test-prolog.scxml)
endif()

if (V8_FOUND)
	add_test(test-ecmascript ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/mmi-browser ${CMAKE_SOURCE_DIR}/test/samples/uscxml/test-ecmascript.scxml)
endif()

if (OPENSCENEGRAPH_FOUND)
	add_executable(test-osg src/test-osg.cpp)
	target_link_libraries(test-osg uscxml)
	set_target_properties(test-osg PROPERTIES FOLDER "Tests")
endif()

add_executable(test-eventdelay src/test-eventdelay.cpp)
target_link_libraries(test-eventdelay uscxml)
add_test(test-eventdelay ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-eventdelay)
set_target_properties(test-eventdelay PROPERTIES FOLDER "Tests")

if (NOT WIN32)
	add_executable(test-arabica-events src/test-arabica-events.cpp)
	target_link_libraries(test-arabica-events uscxml)
	add_test(test-arabica-events ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-arabica-events ${CMAKE_SOURCE_DIR}/test/samples/uscxml/arabica/test-arabica-events.xml)
	set_target_properties(test-arabica-events PROPERTIES FOLDER "Tests")
endif()

add_executable(test-url src/test-url.cpp)
target_link_libraries(test-url uscxml)
add_test(test-url ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-url)
set_target_properties(test-url PROPERTIES FOLDER "Tests")

add_executable(scxml-test-framework-client 
	src/scxml-test-framework-client.cpp)
	target_link_libraries(scxml-test-framework-client uscxml)
set_target_properties(scxml-test-framework-client PROPERTIES FOLDER "Tests")

# add_executable(test-curl-multi-api src/test-curl-multi-api.cpp)
# target_link_libraries(test-curl-multi-api uscxml)
# add_test(test-curl-multi-api ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test-completion)
# set_target_properties(test-curl-multi-api PROPERTIES FOLDER "Tests")
