# minimize SCXML document and run
get_filename_component(TEST_FILE_NAME ${TESTFILE} NAME)

set(COMPILE_CMD_BIN
"-c"
# "-I${PROJECT_SOURCE_DIR}/contrib/src"
# "-I${PROJECT_BINARY_DIR}/deps/xerces-c/include"
# "-I${PROJECT_BINARY_DIR}/deps/libevent/include"
# "-I${PROJECT_BINARY_DIR}/deps/uriparser/include"
# "-I${PROJECT_SOURCE_DIR}/contrib/src/evws"
"-std=c++11"
"-I${CMAKE_BINARY_DIR}"
"-I${PROJECT_BINARY_DIR}"
"-I${PROJECT_SOURCE_DIR}/src"
"${TESTFILE}")

execute_process(COMMAND ${CXX_BIN} ${COMPILE_CMD_BIN} RESULT_VARIABLE CMD_RESULT)
if(CMD_RESULT)
	message(FATAL_ERROR "Error running ${CXX_BIN}")
endif()


