# see http://www.kitware.com/products/html/BuildingExternalProjectsWithCMake2.8.html
# see http://tools.cinemapub.be/opendcp/opendcp-0.19-src/contrib/CMakeLists.txt

include(ExternalProject)
if (MSVC)
	
	externalproject_add(libevent
		URL https://github.com/libevent/libevent/releases/download/release-2.0.22-stable/libevent-2.0.22-stable.tar.gz
		URL_MD5 c4c56f986aa985677ca1db89630a2e11
		BUILD_IN_SOURCE 1
		PREFIX ${CMAKE_BINARY_DIR}/deps/libevent
		CONFIGURE_COMMAND ""
		BUILD_COMMAND nmake -f Makefile.nmake
		INSTALL_COMMAND
			${CMAKE_COMMAND} -E make_directory ${CMAKE_BINARY_DIR}/deps/libevent/lib && 
			${CMAKE_COMMAND} -E copy libevent.lib ${CMAKE_BINARY_DIR}/deps/libevent/lib/ && 
			${CMAKE_COMMAND} -E copy libevent_core.lib ${CMAKE_BINARY_DIR}/deps/libevent/lib/ && 
			${CMAKE_COMMAND} -E copy libevent_extras.lib ${CMAKE_BINARY_DIR}/deps/libevent/lib/ && 
			${CMAKE_COMMAND} -E copy_directory include ${CMAKE_BINARY_DIR}/deps/libevent/include &&
			${CMAKE_COMMAND} -E copy Win32-Code/event2/event-config.h ${CMAKE_BINARY_DIR}/deps/libevent/include/event2/
	)
else ()
	if (UNIX)
		set(FORCE_FPIC "CFLAGS=-fPIC")
	endif()

	externalproject_add(libevent
		URL https://github.com/libevent/libevent/releases/download/release-2.0.22-stable/libevent-2.0.22-stable.tar.gz
		URL_MD5 c4c56f986aa985677ca1db89630a2e11
		BUILD_IN_SOURCE 0
		PREFIX ${CMAKE_BINARY_DIR}/deps/libevent
		PATCH_COMMAND
			${CMAKE_COMMAND} -E copy "${PROJECT_SOURCE_DIR}/contrib/patches/libevent/sierra.kqueue.c" <SOURCE_DIR>/kqueue.c
		CONFIGURE_COMMAND
			 ${FORCE_FPIC} <SOURCE_DIR>/configure --enable-static --enable-shared --disable-openssl --prefix=<INSTALL_DIR>
	)
	
endif()

set(LIBEVENT_INCLUDE_DIR ${CMAKE_BINARY_DIR}/deps/libevent/include)

if (APPLE)
	set(LIBEVENT_LIBRARIES ${CMAKE_BINARY_DIR}/deps/libevent/lib/libevent_core.a)
	list (APPEND LIBEVENT_LIBRARIES ${CMAKE_BINARY_DIR}/deps/libevent/lib/libevent_extra.a)
	list (APPEND LIBEVENT_LIBRARIES ${CMAKE_BINARY_DIR}/deps/libevent/lib/libevent_pthreads.a)
elseif (UNIX)
	set(LIBEVENT_LIBRARIES ${CMAKE_BINARY_DIR}/deps/libevent/lib/libevent_core.a)
	list (APPEND LIBEVENT_LIBRARIES ${CMAKE_BINARY_DIR}/deps/libevent/lib/libevent_extra.a)
	list (APPEND LIBEVENT_LIBRARIES ${CMAKE_BINARY_DIR}/deps/libevent/lib/libevent_pthreads.a)
elseif(WIN32)
	set(LIBEVENT_LIBRARIES ${CMAKE_BINARY_DIR}/deps/libevent/lib/libevent.lib)
else()
	message(FATAL_ERROR "Unknown platform!")
endif()


set(LIBEVENT_BUILT ON)

