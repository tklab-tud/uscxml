#
# This file gets called from the host-specific test files in hosts/. They are
# expected to set the following CTest variables:
#
# CTEST_CMAKE_GENERATOR     - the generator to use for cmake (e.g. "Unix Makefiles")
# CTEST_SITE                - the name of this build-slave
# CTEST_BUILD_CONFIGURATION - "Debug", "Release" ..
# CTEST_BUILD_NAME          - name of the particular build (e.g. "darwin-x86_64 llvm bonjour")
# CMAKE_TOOLCHAIN_FILE      - name of a toolchain file for cross-compiling
#
# CTEST_BUILD_OPTIONS       - parameters to be passed to cmake when preparing the build
#                             these will most likely come from one of the tests/*.ctest files
#
# In addition, we expect the following environment variables to be set:
#
# CTEST_SUBMIT_TYPE - "Experimental", "Nightly", "Continuous"
# USCXML_SOURCE_DIR - full path to the uscxml sources we will work with
#
# We will always build in /tmp/build-*
#

### Custom ctest
# see http://lists.gforge.inria.fr/pipermail/simgrid-commits/2010-November/016461.html

# CTEST_CUSTOM_ERROR_MATCH                          Regular expression for errors during build process
# CTEST_CUSTOM_ERROR_EXCEPTION                      Regular expression for error exceptions during build process
# CTEST_CUSTOM_WARNING_MATCH                        Regular expression for warnings during build process
# CTEST_CUSTOM_WARNING_EXCEPTION                    Regular expression for warning exception during build process
# CTEST_CUSTOM_MAXIMUM_NUMBER_OF_ERRORS             Maximum number of errors to display
# CTEST_CUSTOM_MAXIMUM_NUMBER_OF_WARNINGS           Maximum number of warnings to display
# CTEST_CUSTOM_TESTS_IGNORE                         List of tests to ignore during the Test stage
# CTEST_CUSTOM_MEMCHECK_IGNORE                      List of tests to ignore during the MemCheck stage
# CTEST_CUSTOM_PRE_TEST                             Command to execute before any tests are run during Test stage
# CTEST_CUSTOM_POST_TEST                            Command to execute after any tests are run during Test stage
# CTEST_CUSTOM_MAXIMUM_PASSED_TEST_OUTPUT_SIZE      Maximum size of passed test output
# CTEST_CUSTOM_MAXIMUM_FAILED_TEST_OUTPUT_SIZE      Maximum size of failed test output
# CTEST_CUSTOM_PRE_MEMCHECK                         Command to execute before any tests are run during MemCheck stage
# CTEST_CUSTOM_POST_MEMCHECK                        Command to execute after any tests are run during MemCheck stage
# CTEST_CUSTOM_COVERAGE_EXCLUDE                     Regular expression for excluding files from coverage testing 

if ("$ENV{CTEST_SUBMIT_TYPE}" STREQUAL "")
	set(CTEST_SUBMIT_TYPE "Experimental")
	message(STATUS "ENV{CTEST_SUBMIT_TYPE} is emtpy - defaulting to Experimental")
endif()

if ("$ENV{USCXML_SOURCE_DIR}" STREQUAL "")
	message(FATAL_ERROR "ENV{USCXML_SOURCE_DIR} is emtpy")
endif()

set(CTEST_SOURCE_DIRECTORY $ENV{USCXML_SOURCE_DIR})
set(CTEST_SUBMIT_TYPE $ENV{CTEST_SUBMIT_TYPE})
set(CTEST_BINARY_DIRECTORY "/tmp/build-uscxml-${CTEST_SUBMIT_TYPE}-${CTEST_SCRIPT_NAME}")

if ("$ENV{USCXML_PLUGIN_PATH}" STREQUAL "")
	set(ENV{USCXML_PLUGIN_PATH} /tmp/build-uscxml-${CTEST_SUBMIT_TYPE}-${CTEST_SCRIPT_NAME}/lib)	
endif()

set(CTEST_CUSTOM_MAXIMUM_FAILED_TEST_OUTPUT_SIZE 4194304)
set(CTEST_CUSTOM_MAXIMUM_PASSED_TEST_OUTPUT_SIZE 4194304)

### Coverage and Memory checks? (untested) ################################

if (${CTEST_SUBMIT_TYPE} MATCHES "Nightly")
	find_program(CTEST_COVERAGE_COMMAND NAMES gcov)
	SET(CTEST_CUSTOM_COVERAGE_EXCLUDE
		"${CTEST_SOURCE_DIRECTORY}/contrib/*"
	)
endif()

set(CTEST_CUSTOM_WARNING_EXCEPTION
	".*will never be executed"
)

#find_program(CTEST_MEMORYCHECK_COMMAND NAMES valgrind)
#set(CTEST_MEMORYCHECK_SUPPRESSIONS_FILE ${CTEST_SOURCE_DIRECTORY}/tests/valgrind.supp)

### Versioning Control ###################################################

find_program(CTEST_GIT_COMMAND NAMES git)
if(NOT EXISTS "${CTEST_SOURCE_DIRECTORY}")
  set(CTEST_CHECKOUT_COMMAND "${CTEST_GIT_COMMAND} clone git://github.com/tklab-tud/uscxml.git ${CTEST_SOURCE_DIRECTORY}")
endif()

set(CTEST_UPDATE_COMMAND "${CTEST_GIT_COMMAND}")

### CMake Command line ###################################################

set(CTEST_CONFIGURE_COMMAND "${CMAKE_COMMAND} -LA -DCMAKE_BUILD_TYPE:STRING=${CTEST_BUILD_CONFIGURATION}")
set(CTEST_CONFIGURE_COMMAND "${CTEST_CONFIGURE_COMMAND} \"-G${CTEST_CMAKE_GENERATOR}\"")

if (CTEST_TOOLCHAIN)
	set(CTEST_CONFIGURE_COMMAND "${CTEST_CONFIGURE_COMMAND} -DCMAKE_TOOLCHAIN_FILE=${CTEST_TOOLCHAIN} ${CTEST_BUILD_OPTIONS}")
else()
	set(CTEST_CONFIGURE_COMMAND "${CTEST_CONFIGURE_COMMAND} ${CTEST_BUILD_OPTIONS}")
	#set(CTEST_CONFIGURE_COMMAND "${CTEST_CONFIGURE_COMMAND} -DBUILD_TESTS=ON ${CTEST_BUILD_OPTIONS}")
endif()

set(CTEST_CONFIGURE_COMMAND "${CTEST_CONFIGURE_COMMAND} \"${CTEST_SOURCE_DIRECTORY}\"")

#message(FATAL_ERROR "CTEST_CONFIGURE_COMMAND: ${CTEST_CONFIGURE_COMMAND}")

### Test! ################################################################

# clean build directory for everything but continuous tests
if (NOT RETAIN_BUILD_DIR)
	ctest_empty_binary_directory(${CTEST_BINARY_DIRECTORY})
endif()

ctest_start(${CTEST_SUBMIT_TYPE}) # start testing
#
# I accidentally resynced when running from IDE thrice!
# We will rely on the run_tests.cron script to update to head
#
#ctest_update()                    # synchronize with git head

ctest_configure()                 # run cmake

if(EXISTS "${CTEST_BINARY_DIRECTORY}/CTestCustom.cmake")
	include(${CTEST_BINARY_DIRECTORY}/CTestCustom.cmake)
elseif(EXISTS "${CTEST_BINARY_DIRECTORY}/CTestCustom.ctest")
	include(${CTEST_BINARY_DIRECTORY}/CTestCustom.ctest)
endif()

if (CTEST_TOOLCHAIN)
#
# We do not want to build the tests everytime we compile something, but we cannot
# add a dependency to target "test" as it is unknown to CMake, instead, we introduce
# a new target "ctest" for all tests to depend upon.
#
# But when cross-compiling, we do not add any tests, that is "ctest" depends on nothing,
# in this case, build the whole library without tests.
#
	set(CTEST_BUILD_TARGET "")
else()
	set(CTEST_BUILD_TARGET "")
endif()

ctest_build()                     # build custom target that depends on all the actual tests
if (NOT "${USCXML_EXCLUDE_LABEL_REGEX}" STREQUAL "")
	ctest_test(EXCLUDE_LABEL ${USCXML_EXCLUDE_LABEL_REGEX})
elseif(NOT "${USCXML_INCLUDE_LABEL_REGEX}" STREQUAL "")
	ctest_test(INCLUDE_LABEL ${USCXML_INCLUDE_LABEL_REGEX})
else()
	ctest_test()
endif()


if(CTEST_COVERAGE_COMMAND)
  ctest_coverage()
endif()
if (CTEST_MEMORYCHECK_COMMAND)
  ctest_memcheck()
endif()

ctest_submit()                    # submit
