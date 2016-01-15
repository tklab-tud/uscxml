# convert given file to promela and run spin

set(CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/contrib/cmake)
include("${CMAKE_MODULE_PATH}/FileInformation.cmake")

get_filename_component(TEST_FILE_NAME ${TESTFILE} NAME)
execute_process(COMMAND ${CMAKE_COMMAND} -E make_directory ${OUTDIR})

message(STATUS "${USCXML_TRANSFORM_BIN} -t${TARGETLANG} -i ${TESTFILE} -o ${OUTDIR}/${TEST_FILE_NAME}.machine.c")
execute_process(COMMAND time -p ${USCXML_TRANSFORM_BIN} -t${TARGETLANG} -i ${TESTFILE} -o ${OUTDIR}/${TEST_FILE_NAME}.machine.c RESULT_VARIABLE CMD_RESULT)
if(CMD_RESULT)
	message(FATAL_ERROR "Error running ${USCXML_TRANSFORM_BIN}: ${CMD_RESULT}")
endif()
message(STATUS "time for transforming to c machine")

# message(FATAL_ERROR "PROJECT_BINARY_DIR: ${PROJECT_BINARY_DIR}")

if (${TARGETLANG} STREQUAL "vhdl")

	message(STATUS ${OUTDIR}/${TEST_FILE_NAME})


elseif (${TARGETLANG} STREQUAL "c")
	
	# set(COMPILE_CMD_OBJ
	# "-c" "${OUTDIR}/${TEST_FILE_NAME}.machine.c"
	# "-o" "${OUTDIR}/${TEST_FILE_NAME}.machine.c.o"
	# "-Ofast")
	#
	# message(STATUS "${GPP_BIN} ${COMPILE_CMD_OBJ}")
	# execute_process(
	# 	COMMAND time -p ${GPP_BIN} ${COMPILE_CMD_OBJ}
	# 	WORKING_DIRECTORY ${OUTDIR} RESULT_VARIABLE CMD_RESULT)
	# if(CMD_RESULT)
	# 	message(FATAL_ERROR "Error running g++ ${GPP_BIN}: ${CMD_RESULT}")
	# endif()
	# file (SIZE "${OUTDIR}/${TEST_FILE_NAME}.machine.c.o" BINARY_SIZE)
	# message("Size of compiled unit optimized for speed: ${BINARY_SIZE}")
	#
	# set(COMPILE_CMD_OBJ
	# "-c" "${OUTDIR}/${TEST_FILE_NAME}.machine.c"
	# "-o" "${OUTDIR}/${TEST_FILE_NAME}.machine.c.o"
	# "-Os")
	#
	# message(STATUS "${GPP_BIN} ${COMPILE_CMD_OBJ}")
	# execute_process(
	# 	COMMAND time -p ${GPP_BIN} ${COMPILE_CMD_OBJ}
	# 	WORKING_DIRECTORY ${OUTDIR} RESULT_VARIABLE CMD_RESULT)
	# if(CMD_RESULT)
	# 	message(FATAL_ERROR "Error running g++ ${GPP_BIN}: ${CMD_RESULT}")
	# endif()
	# file (SIZE "${OUTDIR}/${TEST_FILE_NAME}.machine.c.o" BINARY_SIZE)
	# message("Size of compiled unit optimized for size: ${BINARY_SIZE}")
	
	set(COMPILE_CMD_BIN
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

	message(STATUS "${GPP_BIN} ${COMPILE_CMD_BIN}")
	execute_process(
		COMMAND time -p ${GPP_BIN} ${COMPILE_CMD_BIN}
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
endif()

# message(STATUS "${TEST_OUT}")
# file(WRITE ${OUTDIR}/${TEST_FILE_NAME}.pml.out ${TEST_OUT})