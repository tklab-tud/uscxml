# convert given file to promela and run spin

set(CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/contrib/cmake)
include("${CMAKE_MODULE_PATH}/FileInformation.cmake")

get_filename_component(TEST_FILE_NAME ${TESTFILE} NAME)
execute_process(COMMAND ${CMAKE_COMMAND} -E make_directory ${OUTDIR})


# message(FATAL_ERROR "PROJECT_BINARY_DIR: ${PROJECT_BINARY_DIR}")

if (${TARGETLANG} STREQUAL "vhdl")
    if(NOT GHDL_BIN)
        return()
    endif()
    set(VHDL_TESTBENCH_NAME "tb")

    execute_process(COMMAND time -p ${USCXML_TRANSFORM_BIN} -t${TARGETLANG} -i ${TESTFILE} -o ${OUTDIR}/${TEST_FILE_NAME}.machine.vhdl RESULT_VARIABLE CMD_RESULT)
    if (CMD_RESULT)
        message(FATAL_ERROR "Error running ${USCXML_TRANSFORM_BIN}: ${CMD_RESULT}")
    endif ()
    message(STATUS "time for transforming to VHDL machine")

    message(STATUS "GHDL cleaning directory")
    execute_process(
            COMMAND time -p ${GHDL_BIN} --clean
            WORKING_DIRECTORY ${OUTDIR} RESULT_VARIABLE CMD_RESULT)

    message(STATUS "${GHDL_BIN} -a --std=08 ${OUTDIR}/${TEST_FILE_NAME}.machine.vhdl")
    execute_process(
            COMMAND time -p ${GHDL_BIN} -a --std=08 ${OUTDIR}/${TEST_FILE_NAME}.machine.vhdl
            WORKING_DIRECTORY ${OUTDIR} RESULT_VARIABLE CMD_RESULT)
    if (CMD_RESULT)
        message(FATAL_ERROR "Error running ghdl ${GHDL_BIN}: ${CMD_RESULT}")
    endif ()
    message(STATUS "time for syntax check")

    message(STATUS "${GHDL_BIN} -e --std=08 ${VHDL_TESTBENCH_NAME}")
    execute_process(
            COMMAND time -p ${GHDL_BIN} -e --std=08 ${VHDL_TESTBENCH_NAME}
            WORKING_DIRECTORY ${OUTDIR} RESULT_VARIABLE CMD_RESULT)
    if (CMD_RESULT)
        message(FATAL_ERROR "Error running ghdl ${GHDL_BIN}: ${CMD_RESULT}")
    endif ()
    message(STATUS "time for transforming to binary")

    message(STATUS "${GHDL_BIN} -r ${VHDL_TESTBENCH_NAME}")
    execute_process(
            COMMAND time -p ${GHDL_BIN} -r ${VHDL_TESTBENCH_NAME}
            WORKING_DIRECTORY ${OUTDIR} RESULT_VARIABLE CMD_RESULT)
    if (CMD_RESULT)
        message(FATAL_ERROR "Error running ghdl ${GHDL_BIN}: ${CMD_RESULT}")
    endif ()
    message(STATUS "time for transforming to binary")

elseif (${TARGETLANG} STREQUAL "c")

    message(STATUS "${USCXML_TRANSFORM_BIN} -t${TARGETLANG} -i ${TESTFILE} -o ${OUTDIR}/${TEST_FILE_NAME}.machine.c")
    execute_process(COMMAND time -p ${USCXML_TRANSFORM_BIN} -t${TARGETLANG} -i ${TESTFILE} -o ${OUTDIR}/${TEST_FILE_NAME}.machine.c RESULT_VARIABLE CMD_RESULT)
    if (CMD_RESULT)
        message(FATAL_ERROR "Error running ${USCXML_TRANSFORM_BIN}: ${CMD_RESULT}")
    endif ()
    message(STATUS "time for transforming to c machine")

    # set(COMPILE_CMD_OBJ
    # "-c" "${OUTDIR}/${TEST_FILE_NAME}.machine.c"
    # "-o" "${OUTDIR}/${TEST_FILE_NAME}.machine.c.o"
    # "-Ofast" "-ansi" "-m16")
    #
    # message(STATUS "${CC_BIN} ${COMPILE_CMD_OBJ}")
    # execute_process(
    # 	COMMAND time -p ${CC_BIN} ${COMPILE_CMD_OBJ}
    # 	WORKING_DIRECTORY ${OUTDIR} RESULT_VARIABLE CMD_RESULT)
    # if(CMD_RESULT)
    # 	message(FATAL_ERROR "Error running gcc ${CC_BIN}: ${CMD_RESULT}")
    # endif()
    # file (SIZE "${OUTDIR}/${TEST_FILE_NAME}.machine.c.o" BINARY_SIZE)
    # message("Size of compiled unit optimized for speed: ${BINARY_SIZE}")
    #
    # set(COMPILE_CMD_OBJ
    # "-c" "${OUTDIR}/${TEST_FILE_NAME}.machine.c"
    # "-o" "${OUTDIR}/${TEST_FILE_NAME}.machine.c.o"
    # "-Os" "-ansi" "-m16")
    #
    # message(STATUS "${CC_BIN} ${COMPILE_CMD_OBJ}")
    # execute_process(
    # 	COMMAND time -p ${CC_BIN} ${COMPILE_CMD_OBJ}
    # 	WORKING_DIRECTORY ${OUTDIR} RESULT_VARIABLE CMD_RESULT)
    # if(CMD_RESULT)
    # 	message(FATAL_ERROR "Error running gcc ${CC_BIN}: ${CMD_RESULT}")
    # endif()
    # file (SIZE "${OUTDIR}/${TEST_FILE_NAME}.machine.c.o" BINARY_SIZE)
    # message("Size of compiled unit optimized for size: ${BINARY_SIZE}")

    set(COMPILE_CMD_BIN
            "-O0"
            "-std=c++11"
            "-Wl,-search_paths_first"
            "-Wl,-headerpad_max_install_names"
            "-o" "${OUTDIR}/${TEST_FILE_NAME}"
            "-L${CMAKE_LIBRARY_OUTPUT_DIRECTORY}"
            "-L${PROJECT_BINARY_DIR}/deps/xerces-c/lib"
            "-luscxml"
            "-lxerces-c"
            "-include" "${OUTDIR}/${TEST_FILE_NAME}.machine.c"
            "-I${PROJECT_SOURCE_DIR}/contrib/src"
            "-I${PROJECT_SOURCE_DIR}/src"
            "-I${PROJECT_BINARY_DIR}"
            "-I${XercesC_INCLUDE_DIRS}"
            "-I${URIPARSER_INCLUDE_DIR}"
            "-I${LIBEVENT_INCLUDE_DIR}"
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
endif ()

# message(STATUS "${TEST_OUT}")
# file(WRITE ${OUTDIR}/${TEST_FILE_NAME}.pml.out ${TEST_OUT})