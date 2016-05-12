# see http://www.kitware.com/products/html/BuildingExternalProjectsWithCMake2.8.html
# see http://tools.cinemapub.be/opendcp/opendcp-0.19-src/contrib/CMakeLists.txt

# not functional yet

include(ExternalProject)
if (UNIX)
	externalproject_add(xalan-c
		URL http://ftp.halifax.rwth-aachen.de/apache/xalan/xalan-c/sources/xalan_c-1.11-src.tar.gz
		URL_MD5 9227d3e7ab375da3c643934b33a585b8
		BUILD_IN_SOURCE 0
		PREFIX ${CMAKE_BINARY_DIR}/deps/xalan-c
		CONFIGURE_COMMAND 
			"<SOURCE_DIR>/c/configure" 
			"--enable-static" 
			"--prefix=<INSTALL_DIR>"
	)
	
	set(XALANC_INCLUDE_DIR ${CMAKE_BINARY_DIR}/deps/xalan-c/include)
	
	if (APPLE)
		set(XALANC_LIBRARY ${CMAKE_BINARY_DIR}/deps/xalan-c/lib/xalan-c.a)
	elseif(UNIX)
		set(XALANC_LIBRARY ${CMAKE_BINARY_DIR}/deps/xalan-c/lib/xalan-c.a)
	elseif(WIN32)
		set(XALANC_LIBRARY ${CMAKE_BINARY_DIR}/deps/xalan-c/lib/xalan-c.lib)
	else()
		message(FATAL_ERROR "Unknown platform!")
	endif()
	
endif()