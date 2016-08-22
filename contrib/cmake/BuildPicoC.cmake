include(ExternalProject)

if ("${CMAKE_GENERATOR}" STREQUAL "Xcode")
	set(PICOC_LIBNAME "Debug/libpicoc.a")
elseif (WIN32)
	set(PICOC_LIBNAME "picoc.lib")
elseif(UNIX)
	set(PICOC_LIBNAME "libpicoc.a")
endif()

externalproject_add(picoc
	GIT_REPOSITORY https://github.com/zsaleeba/picoc.git
	BUILD_IN_SOURCE 0
	PREFIX ${CMAKE_BINARY_DIR}/deps/picoc
	UPDATE_COMMAND ""
	PATCH_COMMAND 
	${CMAKE_COMMAND} -E copy "${PROJECT_SOURCE_DIR}/contrib/patches/picoc/CMakeLists.txt" <SOURCE_DIR>/CMakeLists.txt &&
	${CMAKE_COMMAND} -E copy "${PROJECT_SOURCE_DIR}/contrib/patches/picoc/platform.h" <SOURCE_DIR>/platform.h
	CONFIGURE_COMMAND 
		${CMAKE_COMMAND} 
		-G ${CMAKE_GENERATOR}
		-DCMAKE_BUILD_TYPE=Release
		${CMAKE_PARAM_TOOLCHAIN} 
		${CMAKE_PARAM_ANDROID_ABI}
		${CMAKE_PARAM_API_LEVEL}
		${CMAKE_PARAM_SHARED}
		-DCMAKE_VERBOSE_MAKEFILE=OFF
		-DBUILD_SHARED_LIBS=OFF
		<SOURCE_DIR>
	INSTALL_COMMAND ""
)

set(PICOC_INCLUDE_DIR ${CMAKE_BINARY_DIR}/deps/picoc/src/picoc)
set(PICOC_LIBRARY ${CMAKE_BINARY_DIR}/deps/picoc/src/picoc-build/${PICOC_LIBNAME})

set(PICOC_BUILT ON)


