add_executable(test-predicates src/test-predicates.cpp)
target_link_libraries(test-predicates uscxml)
add_test(test-predicates ${CURRENT_BINARY_DIR}/test-predicates ${CMAKE_SOURCE_DIR}/test/src/test-predicates.scxml)
set_target_properties(test-predicates PROPERTIES FOLDER "Tests")

add_executable(test-execution src/test-execution.cpp)
target_link_libraries(test-execution uscxml)
add_test(test-execution ${CURRENT_BINARY_DIR}/test-execution ${CMAKE_SOURCE_DIR}/test/src/test-execution.scxml)
set_target_properties(test-execution PROPERTIES FOLDER "Tests")

add_executable(test-apache-commons src/test-apache-commons.cpp)
target_link_libraries(test-apache-commons uscxml)
add_test(test-apache-commons ${CURRENT_BINARY_DIR}/test-apache-commons ${CMAKE_SOURCE_DIR}/test/samples/apache)
set_target_properties(test-apache-commons PROPERTIES FOLDER "Tests")

add_executable(test-ecmascript-v8 src/test-ecmascript-v8.cpp)
target_link_libraries(test-ecmascript-v8 uscxml)
add_test(test-ecmascript-v8 ${CURRENT_BINARY_DIR}/test-ecmascript-v8 ${CMAKE_SOURCE_DIR}/test/src/test-ecmascript.scxml)
set_target_properties(test-ecmascript-v8 PROPERTIES FOLDER "Tests")

add_executable(test-communication src/test-communication.cpp)
target_link_libraries(test-communication uscxml)
add_test(test-communication test-communication)
set_target_properties(test-communication PROPERTIES FOLDER "Tests")

add_executable(test-eventdelay src/test-eventdelay.cpp)
target_link_libraries(test-eventdelay uscxml)
add_test(test-eventdelay test-eventdelay)
set_target_properties(test-eventdelay PROPERTIES FOLDER "Tests")

add_executable(test-completion src/test-completion.cpp)
target_link_libraries(test-completion uscxml)
add_test(test-completion ${CMAKE_SOURCE_DIR}/test/src/test-donedata.scxml)
set_target_properties(test-completion PROPERTIES FOLDER "Tests")
