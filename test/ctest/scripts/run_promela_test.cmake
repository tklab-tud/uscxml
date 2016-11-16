# convert given file to promela and run spin

get_filename_component(TEST_FILE_NAME ${TESTFILE} NAME)
execute_process(COMMAND ${CMAKE_COMMAND} -E make_directory ${OUTDIR})

set(ENV{USCXML_PROMELA_TRANSITION_TRACE} "TRUE")
set(ENV{USCXML_PROMELA_TRANSITION_DEBUG} "TRUE")

message(STATUS "${USCXML_TRANSFORM_BIN} -tpml -i ${TESTFILE} -o ${OUTDIR}/${TEST_FILE_NAME}.pml")
execute_process(COMMAND time -p ${USCXML_TRANSFORM_BIN} -tpml -i ${TESTFILE} -o ${OUTDIR}/${TEST_FILE_NAME}.pml RESULT_VARIABLE CMD_RESULT)
if(CMD_RESULT)
	message(FATAL_ERROR "Error running ${USCXML_TRANSFORM_BIN}: ${CMD_RESULT}")
endif()
message(STATUS "time for transforming to promela")

message(STATUS "${SPIN_BIN} -a ${OUTDIR}/${TEST_FILE_NAME}.pml")
execute_process(COMMAND time -p ${SPIN_BIN} -a ${OUTDIR}/${TEST_FILE_NAME}.pml WORKING_DIRECTORY ${OUTDIR} RESULT_VARIABLE CMD_RESULT)
if(CMD_RESULT)
	message(FATAL_ERROR "Error running spin ${SPIN_BIN}: ${CMD_RESULT}")
endif()
message(STATUS "time for transforming to c")

message(STATUS "${CC_BIN} -DMEMLIM=1024 -DVECTORSZ=2048 -O2 -DXUSAFE -w -o ${OUTDIR}/pan ${OUTDIR}/pan.c")
execute_process(COMMAND time -p ${CC_BIN} -DMEMLIM=1024 -DVECTORSZ=2048 -O2 -DXUSAFE -w -o ${OUTDIR}/pan ${OUTDIR}/pan.c WORKING_DIRECTORY ${OUTDIR} RESULT_VARIABLE CMD_RESULT)
if(CMD_RESULT)
	message(FATAL_ERROR "Error running gcc ${CC_BIN}: ${CMD_RESULT}")
endif()
message(STATUS "time for transforming to binary")

message(STATUS "${OUTDIR}/pan -m10000 -a")
execute_process(COMMAND time -p ${OUTDIR}/pan -m10000 -a WORKING_DIRECTORY ${OUTDIR} RESULT_VARIABLE CMD_RESULT)
if(CMD_RESULT)
	message(FATAL_ERROR "Error running pan: ${CMD_RESULT}")
endif()
message(STATUS "time for verification")

# message(STATUS "${TEST_OUT}")
# file(WRITE ${OUTDIR}/${TEST_FILE_NAME}.pml.out ${TEST_OUT})