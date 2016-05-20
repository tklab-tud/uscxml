include(ExternalProject)

if (WIN32)
	add_definitions("-DCURL_STATICLIB")
endif()

if (MSVC)
	
	# see https://en.wikipedia.org/wiki/Visual_C%2B%2B
	set(VC_VERSION 14)
	
	if (OFF)
	elseif(MSVC_VERSION LESS 1310)
		message(FATAL_ERROR "MSVC 7.1 or higher is required")
	elseif(MSVC_VERSION LESS 1400)
		set(VC_VERSION 7)
	elseif(MSVC_VERSION LESS 1500)
		set(VC_VERSION 8)
	elseif(MSVC_VERSION LESS 1600)
		set(VC_VERSION 9)
	elseif(MSVC_VERSION LESS 1700)
		set(VC_VERSION 10)
	elseif(MSVC_VERSION LESS 1800)
		set(VC_VERSION 11)
	elseif (MSVC_VERSION LESS 1900)
		set(VC_VERSION 12)
	endif()
		
	if( CMAKE_SIZEOF_VOID_P EQUAL 8 )
		externalproject_add(libcurl
			URL https://curl.haxx.se/download/curl-7.48.0.tar.gz
			URL_MD5 b2cac71029d28cb989150bac72aafab5
			BUILD_IN_SOURCE 1
			PREFIX ${CMAKE_BINARY_DIR}/deps/libcurl
			CONFIGURE_COMMAND ""
			BUILD_COMMAND cd winbuild && nmake /f Makefile.vc mode=static MACHINE=x64 VC=${VC_VERSION}
			INSTALL_COMMAND ${CMAKE_COMMAND} -E copy_directory builds/libcurl-vc${VC_VERSION}-x64-release-static-ipv6-sspi-winssl ${CMAKE_BINARY_DIR}/deps/libcurl/
		)
	else()
		externalproject_add(libcurl
			URL https://curl.haxx.se/download/curl-7.48.0.tar.gz
			URL_MD5 b2cac71029d28cb989150bac72aafab5
			BUILD_IN_SOURCE 1
			PREFIX ${CMAKE_BINARY_DIR}/deps/libcurl
			CONFIGURE_COMMAND ""
			BUILD_COMMAND cd winbuild && nmake /f Makefile.vc mode=static MACHINE=x86 VC=${VC_VERSION}
			INSTALL_COMMAND ${CMAKE_COMMAND} -E copy_directory builds/libcurl-vc${VC_VERSION}-x86-release-static-ipv6-sspi-winssl ${CMAKE_BINARY_DIR}/deps/libcurl/
		)
	endif()
else()
	externalproject_add(libcurl
		URL https://curl.haxx.se/download/curl-7.48.0.tar.gz
		URL_MD5 b2cac71029d28cb989150bac72aafab5
		BUILD_IN_SOURCE 0
		PREFIX ${CMAKE_BINARY_DIR}/deps/libcurl
		CONFIGURE_COMMAND 
			"<SOURCE_DIR>/configure" 
			"--without-ssl"
			"--enable-shared"
			"--prefix=<INSTALL_DIR>"
	)
endif()

set(LIBCURL_INCLUDE_DIR ${CMAKE_BINARY_DIR}/deps/libcurl/include)

if (APPLE)
	set(LIBCURL_LIBRARY ${CMAKE_BINARY_DIR}/deps/libcurl/lib/libcurl.a)
elseif(UNIX)
	set(LIBCURL_LIBRARY ${CMAKE_BINARY_DIR}/deps/libcurl/lib/libcurl.a)
elseif(WIN32)
	set(LIBCURL_LIBRARY ${CMAKE_BINARY_DIR}/deps/libcurl/lib/libcurl_a.lib)
else()
	message(FATAL_ERROR "Unknown platform!")
endif()


set(LIBCURL_BUILT ON)

