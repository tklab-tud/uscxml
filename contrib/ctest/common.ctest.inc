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

if ("$ENV{CTEST_SUBMIT_TYPE}" STREQUAL "")
	message(FATAL_ERROR "ENV{CTEST_SUBMIT_TYPE} is emtpy")
endif()

if ("$ENV{USCXML_SOURCE_DIR}" STREQUAL "")
	message(FATAL_ERROR "ENV{USCXML_SOURCE_DIR} is emtpy")
endif()

set(CTEST_SOURCE_DIRECTORY $ENV{USCXML_SOURCE_DIR})
set(CTEST_SUBMIT_TYPE $ENV{CTEST_SUBMIT_TYPE})
set(CTEST_BINARY_DIRECTORY "/tmp/build-uscxml-${CTEST_SUBMIT_TYPE}-${CTEST_SCRIPT_NAME}")

set(CTEST_CUSTOM_MAXIMUM_FAILED_TEST_OUTPUT_SIZE 1048576)
set(CTEST_CUSTOM_MAXIMUM_PASSED_TEST_OUTPUT_SIZE 1048576)

### Coverage and Memory checks? (untested) ################################

#find_program(CTEST_COVERAGE_COMMAND NAMES gcov)

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
#if (NOT ${CTEST_SUBMIT_TYPE} MATCHES ".*Continuous.*")
	ctest_empty_binary_directory(${CTEST_BINARY_DIRECTORY})
#endif()

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
ctest_test()                      # run tests

if(CTEST_COVERAGE_COMMAND)
  ctest_coverage()
endif()
if (CTEST_MEMORYCHECK_COMMAND)
  ctest_memcheck()
endif()

ctest_submit()                    # submit
