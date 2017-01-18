# see test/CMakeLists.txt for passed variables

get_filename_component(TEST_FILE_NAME ${TESTFILE} NAME)
get_filename_component(TEST_FILE_NAME_WE ${TESTFILE} NAME_WE)
set(JAVA_PACKAGE_NAME "org.uscxml.gen")
set(JAVA_PACKAGE_PATH "org/uscxml/gen")

execute_process(COMMAND ${CMAKE_COMMAND} -E make_directory ${OUTDIR}/${JAVA_PACKAGE_PATH})

# message(FATAL_ERROR "PROJECT_BINARY_DIR: ${PROJECT_BINARY_DIR}")

execute_process(
	COMMAND time -p ${USCXML_TRANSFORM_BIN} -t${TARGETLANG} -i ${TESTFILE} -o ${OUTDIR}/${JAVA_PACKAGE_PATH}/TestStateChartBase.java -XpackageName=${JAVA_PACKAGE_NAME} -XjavaVersion=5
	RESULT_VARIABLE CMD_RESULT
)
if (CMD_RESULT)
    message(FATAL_ERROR "Error running ${USCXML_TRANSFORM_BIN}: ${CMD_RESULT}")
endif ()
message(STATUS "time for transforming to Java machine")

execute_process(COMMAND
	${ANT_BIN}
	-Dtest.file=${W3C_TEST}
	-Dgenerated.dir=${OUTDIR}
	WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}/contrib/java/bindings
	RESULT_VARIABLE CMD_RESULT
	OUTPUT_VARIABLE CMD_OUTPUT
)

if (CMD_RESULT)
    message(FATAL_ERROR "Error running ${ANT_BIN} : ${CMD_RESULT} ${PROJECT_SOURCE_DIR}/contrib/java/bindings ${CMD_OUTPUT}")
endif ()
