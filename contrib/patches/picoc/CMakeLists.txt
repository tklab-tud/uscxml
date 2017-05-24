cmake_minimum_required(VERSION 2.8.4)
project(picoc)

# include_directories(${PROJECT_SOURCE_DIR}/include)

set(CMAKE_POSITION_INDEPENDENT_CODE ON)

file(GLOB PICOC_FILES 
	${PROJECT_SOURCE_DIR}/*.h
	${PROJECT_SOURCE_DIR}/*.c
	${PROJECT_SOURCE_DIR}/cstdlib/*.h
	${PROJECT_SOURCE_DIR}/cstdlib/*.c)

	if (UNIX)
		add_definitions("-DUNIX_HOST")
		list (APPEND PICOC_FILES ${PROJECT_SOURCE_DIR}/platform/library_unix.c)
		list (APPEND PICOC_FILES ${PROJECT_SOURCE_DIR}/platform/platform_unix.c)
	endif()
	if (WIN32)
		list (REMOVE_ITEM PICOC_FILES ${PROJECT_SOURCE_DIR}/cstdlib/unistd.c)
		list (APPEND PICOC_FILES ${PROJECT_SOURCE_DIR}/platform/platform_msvc.c)
		list (APPEND PICOC_FILES ${PROJECT_SOURCE_DIR}/platform/library_msvc.c)
	endif()

add_library(picoc ${PICOC_FILES})

# set_target_properties(uriparser PROPERTIES PREFIX "")
