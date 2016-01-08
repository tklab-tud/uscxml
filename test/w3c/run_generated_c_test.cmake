# convert given file to promela and run spin

get_filename_component(TEST_FILE_NAME ${TESTFILE} NAME)
execute_process(COMMAND ${CMAKE_COMMAND} -E make_directory ${OUTDIR})

message(STATUS "${USCXML_TRANSFORM_BIN} -tc -i ${TESTFILE} -o ${OUTDIR}/${TEST_FILE_NAME}.machine.c")
execute_process(COMMAND time -p ${USCXML_TRANSFORM_BIN} -tc -i ${TESTFILE} -o ${OUTDIR}/${TEST_FILE_NAME}.machine.c RESULT_VARIABLE CMD_RESULT)
if(CMD_RESULT)
	message(FATAL_ERROR "Error running ${USCXML_TRANSFORM_BIN}: ${CMD_RESULT}")
endif()
message(STATUS "time for transforming to c machine")

# message(FATAL_ERROR "PROJECT_BINARY_DIR: ${PROJECT_BINARY_DIR}")

set(COMPILE_CMD
"-o" "${OUTDIR}/${TEST_FILE_NAME}"
"-Ofast"
"-L${CMAKE_LIBRARY_OUTPUT_DIRECTORY}"
"-luscxml64" 
"-include" "${OUTDIR}/${TEST_FILE_NAME}.machine.c"
"-I${PROJECT_SOURCE_DIR}/contrib/prebuilt/${USCXML_PLATFORM_ID}/include"
"-I${PROJECT_SOURCE_DIR}/contrib/prebuilt/${USCXML_PLATFORM_ID}/include/arabica"
"-I${PROJECT_SOURCE_DIR}/contrib/prebuilt/include"
"-I${CMAKE_BINARY_DIR}"
"-I${PROJECT_BINARY_DIR}"
"-I${PROJECT_SOURCE_DIR}/src"
"-Wl,-rpath,${CMAKE_LIBRARY_OUTPUT_DIRECTORY}"
"-DAUTOINCLUDE_TEST=ON"
"${SCAFFOLDING_FOR_GENERATED_C}")

message(STATUS "${GPP_BIN} ${COMPILE_CMD}")
execute_process(
	COMMAND time -p ${GPP_BIN} ${COMPILE_CMD}
	WORKING_DIRECTORY ${OUTDIR} RESULT_VARIABLE CMD_RESULT)
if(CMD_RESULT)
	message(FATAL_ERROR "Error running g++ ${GPP_BIN}: ${CMD_RESULT}")
endif()
message(STATUS "time for transforming to binary")

message(STATUS "${OUTDIR}/${TEST_FILE_NAME}")
execute_process(
	COMMAND time -p ${OUTDIR}/${TEST_FILE_NAME} 
	WORKING_DIRECTORY ${OUTDIR} 
	RESULT_VARIABLE CMD_RESULT)
if(CMD_RESULT)
	message(FATAL_ERROR "Error running generated c test: ${CMD_RESULT}")
endif()
message(STATUS "time for execution")

# message(STATUS "${TEST_OUT}")
# file(WRITE ${OUTDIR}/${TEST_FILE_NAME}.pml.out ${TEST_OUT})