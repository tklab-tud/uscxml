# see test/CMakeLists.txt for passed variables

get_filename_component(TEST_FILE_NAME ${TESTFILE} NAME)
execute_process(COMMAND ${CMAKE_COMMAND} -E make_directory ${OUTDIR})

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
