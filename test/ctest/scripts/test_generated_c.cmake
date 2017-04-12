# see test/CMakeLists.txt for passed variables

set(CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/contrib/cmake)
include("${CMAKE_MODULE_PATH}/FileInformation.cmake")

get_filename_component(TEST_FILE_NAME ${TESTFILE} NAME)
execute_process(COMMAND ${CMAKE_COMMAND} -E make_directory ${OUTDIR})

# message(FATAL_ERROR "PROJECT_BINARY_DIR: ${PROJECT_BINARY_DIR}")

message(STATUS "${USCXML_TRANSFORM_BIN} -t${TARGETLANG} -i ${TESTFILE} -o ${OUTDIR}/${TEST_FILE_NAME}.machine.c")
execute_process(COMMAND time -p ${USCXML_TRANSFORM_BIN} -t${TARGETLANG} -i ${TESTFILE} -o ${OUTDIR}/${TEST_FILE_NAME}.machine.c RESULT_VARIABLE CMD_RESULT)
if (CMD_RESULT)
    message(FATAL_ERROR "Error running ${USCXML_TRANSFORM_BIN}: ${CMD_RESULT}")
endif ()
message(STATUS "time for transforming to c machine")

set(LIBRARY_PATH "-L${CMAKE_LIBRARY_OUTPUT_DIRECTORY}" "-L/opt/local/lib")
set(LIBRARY_FILE "-luscxml")
set(INCLUDE_PATH 
	"-I${PROJECT_SOURCE_DIR}/contrib/src"
	"-I${PROJECT_SOURCE_DIR}/src"
	"-I${PROJECT_BINARY_DIR}"
	"-I${LIBEVENT_INCLUDE_DIR}"
)

# if (WITH_DM_ECMA_JSC AND JSC_INCLUDE_DIR)
# 	message(FATAL_ERROR "${JSC_INCLUDE_DIR}")
# 	if (JSC_LIBRARY)
# 		list (APPEND LIBRARY_FILE ${JSC_LIBRARY})
# 	endif()
# 	list (APPEND INCLUDE_PATH "-I${JSC_INCLUDE_DIR}")
# endif()
#
# if (WITH_DM_ECMA_V8 AND V8_INCLUDE_DIR)
# 	# message(FATAL_ERROR "${V8_INCLUDE_DIR}")
# 	# list (APPEND LIBRARY_FILE ${V8_LIBRARY})
# 	list (APPEND INCLUDE_PATH "-I${V8_INCLUDE_DIR}")
# endif()

set(COMPILE_CMD_BIN
        "-O0"
        "-std=c++11"
        "-Wl,-search_paths_first"
        "-Wl,-headerpad_max_install_names"
        "-o" "${OUTDIR}/${TEST_FILE_NAME}"
        ${LIBRARY_PATH}
        ${LIBRARY_FILE}
        ${INCLUDE_PATH}
        "-include" "${OUTDIR}/${TEST_FILE_NAME}.machine.c"
        "-Wl,-rpath,${CMAKE_LIBRARY_OUTPUT_DIRECTORY}"
        "-DAUTOINCLUDE_TEST=ON"
        "${SCAFFOLDING_FOR_GENERATED_C}")

message(STATUS "${CXX_BIN} ${COMPILE_CMD_BIN}")
execute_process(
        COMMAND time -p ${CXX_BIN} ${COMPILE_CMD_BIN}
        WORKING_DIRECTORY ${OUTDIR} RESULT_VARIABLE CMD_RESULT)
if (CMD_RESULT)
    message(FATAL_ERROR "Error running g++ ${CXX_BIN}: ${CMD_RESULT}")
endif ()
message(STATUS "time for transforming to binary")

message(STATUS "${OUTDIR}/${TEST_FILE_NAME}")
execute_process(
        COMMAND time -p ${OUTDIR}/${TEST_FILE_NAME}
        WORKING_DIRECTORY ${OUTDIR}
        RESULT_VARIABLE CMD_RESULT)
if (CMD_RESULT)
    message(FATAL_ERROR "Error running generated c test: ${CMD_RESULT}")
endif ()
message(STATUS "time for execution")

# message(STATUS "${TEST_OUT}")
# file(WRITE ${OUTDIR}/${TEST_FILE_NAME}.pml.out ${TEST_OUT})