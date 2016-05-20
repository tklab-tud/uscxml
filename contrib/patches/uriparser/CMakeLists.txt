cmake_minimum_required(VERSION 2.8.4)
project(uriparser)

set(BUILD_SHARED_LIBS OFF)

include_directories(${PROJECT_SOURCE_DIR}/include)

file(GLOB URIPARSER_FILES 
	${PROJECT_SOURCE_DIR}/src/*.h
	${PROJECT_SOURCE_DIR}/src/*.c)

add_library(uriparser ${URIPARSER_FILES})

# set_target_properties(uriparser PROPERTIES PREFIX "")
