# convert given file to promela and run spin

get_filename_component(TEST_FILE_NAME ${TESTFILE} NAME)
execute_process(COMMAND ${CMAKE_COMMAND} -E make_directory ${OUTDIR})

set(ENV{USCXML_PROMELA_TRANSITION_TRACE} "TRUE")
set(ENV{USCXML_PROMELA_TRANSITION_DEBUG} "TRUE")

execute_process(COMMAND ${USCXML_TRANSFORM_BIN} -tpml -i ${TESTFILE} -o ${OUTDIR}/${TEST_FILE_NAME}.pml RESULT_VARIABLE CMD_RESULT)
if(CMD_RESULT)
	message(FATAL_ERROR "Error running ${USCXML_TRANSFORM_BIN}: ${CMD_RESULT}")
endif()

execute_process(COMMAND ${SPIN_BIN} -a ${OUTDIR}/${TEST_FILE_NAME}.pml WORKING_DIRECTORY ${OUTDIR} RESULT_VARIABLE CMD_RESULT)
if(CMD_RESULT)
	message(FATAL_ERROR "Error running spin ${SPIN_BIN}: ${CMD_RESULT}")
endif()

execute_process(COMMAND ${GCC_BIN} -DMEMLIM=1024 -DVECTORSZ=8192 -O2 -DXUSAFE -w -o ${OUTDIR}/pan ${OUTDIR}/pan.c WORKING_DIRECTORY ${OUTDIR} RESULT_VARIABLE CMD_RESULT)
if(CMD_RESULT)
	message(FATAL_ERROR "Error running gcc ${GCC_BIN}: ${CMD_RESULT}")
endif()

execute_process(COMMAND ${OUTDIR}/pan -m10000 -a WORKING_DIRECTORY ${OUTDIR} RESULT_VARIABLE CMD_RESULT)
if(CMD_RESULT)
	message(FATAL_ERROR "Error running pan: ${CMD_RESULT}")
endif()
#
# message(STATUS "${TEST_OUT}")
# file(WRITE ${OUTDIR}/${TEST_FILE_NAME}.pml.out ${TEST_OUT})