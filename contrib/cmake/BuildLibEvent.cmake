# see http://www.kitware.com/products/html/BuildingExternalProjectsWithCMake2.8.html
# see http://tools.cinemapub.be/opendcp/opendcp-0.19-src/contrib/CMakeLists.txt

include(ExternalProject)
if (UNIX)
	externalproject_add(libevent
		URL https://github.com/libevent/libevent/releases/download/release-2.0.22-stable/libevent-2.0.22-stable.tar.gz
		URL_MD5 c4c56f986aa985677ca1db89630a2e11
		BUILD_IN_SOURCE 0
		PREFIX ${CMAKE_BINARY_DIR}/deps/libevent
		CONFIGURE_COMMAND 
			"<SOURCE_DIR>/configure" 
			"--enable-static" 
			"--disable-openssl"
			"--prefix=<INSTALL_DIR>"
	)
elseif (WIN32)
	
	
	externalproject_add(libevent
		URL https://github.com/libevent/libevent/releases/download/release-2.0.22-stable/libevent-2.0.22-stable.tar.gz
		URL_MD5 c4c56f986aa985677ca1db89630a2e11
		BUILD_IN_SOURCE 1
		PREFIX ${CMAKE_BINARY_DIR}/deps/libevent
		CONFIGURE_COMMAND ""
		BUILD_COMMAND nmake -f Makefile.nmake
		INSTALL_COMMAND
			${CMAKE_COMMAND} -E make_directory ${CMAKE_BINARY_DIR}/deps/libevent/lib && 
			${CMAKE_COMMAND} -E copy libevent.lib libevent_core.lib libevent_extras.lib ${CMAKE_BINARY_DIR}/deps/libevent/lib/ && 
			${CMAKE_COMMAND} -E copy_directory include ${CMAKE_BINARY_DIR}/deps/libevent/include
			${CMAKE_COMMAND} -E copy Win32-Code/event2 ${CMAKE_BINARY_DIR}/deps/libevent/include/event2
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

