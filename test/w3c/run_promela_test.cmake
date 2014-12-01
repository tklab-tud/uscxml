# convert given file to promela and run spin

get_filename_component(TEST_FILE_NAME ${TESTFILE} NAME)

execute_process(COMMAND ${USCXML_TRANSFORM_BIN} -i ${TESTFILE} -o ${OUTDIR}/${TEST_FILE_NAME}.pml RESULT_VARIABLE CMD_RESULT)
if(CMD_RESULT)
	message(FATAL_ERROR "Error running ${USCXML_TRANSFORM_BIN}: ${CMD_RESULT}")
endif()

execute_process(COMMAND ${SPIN_BIN} -a ${OUTDIR}/${TEST_FILE_NAME}.pml RESULT_VARIABLE CMD_RESULT)
if(CMD_RESULT)
	message(FATAL_ERROR "Error running ${SPIN_BIN}: ${CMD_RESULT}")
endif()

execute_process(COMMAND ${GCC_BIN} -DMEMLIM=1024 -DVECTORSZ=2048 -O2 -DXUSAFE -w -o ${OUTDIR}/pan ${OUTDIR}/pan.c RESULT_VARIABLE CMD_RESULT)
if(CMD_RESULT)
	message(FATAL_ERROR "Error running ${GCC_BIN}: ${CMD_RESULT}")
endif()

execute_process(COMMAND ${OUTDIR}/pan -m10000 -a RESULT_VARIABLE CMD_RESULT)
if(CMD_RESULT)
	message(FATAL_ERROR "Error running pan: ${CMD_RESULT}")
endif()
