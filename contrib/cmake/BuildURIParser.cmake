include(ExternalProject)
if (UNIX)
	externalproject_add(uriparser
		URL http://ufpr.dl.sourceforge.net/project/uriparser/Sources/0.8.4/uriparser-0.8.4.zip
		URL_MD5 a24c9ba0fd1a2c6c75d02859bf337cfa
		BUILD_IN_SOURCE 0
		PREFIX ${CMAKE_BINARY_DIR}/deps/uriparser
		CONFIGURE_COMMAND 
			"CFLAGS=-fPIC"
			"<SOURCE_DIR>/configure" 
			"--disable-test"
			"--disable-doc"
			"--enable-static"
			"--prefix=<INSTALL_DIR>"
	)
elseif(WIN32)
	set(VSPROJECT_PATH "win32/Visual_Studio_2005")
	
	if( CMAKE_SIZEOF_VOID_P EQUAL 8 )
		externalproject_add(uriparser
			URL http://ufpr.dl.sourceforge.net/project/uriparser/Sources/0.8.4/uriparser-0.8.4.zip
			URL_MD5 a24c9ba0fd1a2c6c75d02859bf337cfa
			BUILD_IN_SOURCE 1
			PREFIX ${CMAKE_BINARY_DIR}/deps/uriparser
			CONFIGURE_COMMAND ""
			BUILD_COMMAND cd ${VSPROJECT_PATH} && devenv /build Release|x64 uriparser.sln
			INSTALL_COMMAND ${CMAKE_COMMAND} -E make_directory ${CMAKE_BINARY_DIR}/deps/uriparser/lib && ${CMAKE_COMMAND} -E copy win32/uriparser.lib ${CMAKE_BINARY_DIR}/deps/uriparser/lib && ${CMAKE_COMMAND} -E copy_directory include ${CMAKE_BINARY_DIR}/deps/uriparser/include
		)
	else()
		externalproject_add(uriparser
			URL http://ufpr.dl.sourceforge.net/project/uriparser/Sources/0.8.4/uriparser-0.8.4.zip
			URL_MD5 a24c9ba0fd1a2c6c75d02859bf337cfa
			BUILD_IN_SOURCE 1
			PREFIX ${CMAKE_BINARY_DIR}/deps/uriparser
			CONFIGURE_COMMAND ""
			BUILD_COMMAND cd ${VSPROJECT_PATH} && devenv /Upgrade uriparser.vcproj && msbuild /p:Configuration=Release /p:Platform=Win32 /t:build uriparser.vcxproj
			INSTALL_COMMAND ${CMAKE_COMMAND} -E make_directory ${CMAKE_BINARY_DIR}/deps/uriparser/lib && ${CMAKE_COMMAND} -E copy win32/uriparser.lib ${CMAKE_BINARY_DIR}/deps/uriparser/lib && ${CMAKE_COMMAND} -E copy_directory include ${CMAKE_BINARY_DIR}/deps/uriparser/include
		)
	endif()
	
endif()

set(URIPARSER_INCLUDE_DIR ${CMAKE_BINARY_DIR}/deps/uriparser/include)

if (UNIX)
	set(URIPARSER_LIBRARY ${CMAKE_BINARY_DIR}/deps/uriparser/lib/liburiparser.a)
elseif(WIN32)
	set(URIPARSER_LIBRARY ${CMAKE_BINARY_DIR}/deps/uriparser/lib/uriparser.lib)
else()
	message(FATAL_ERROR "Unknown platform!")
endif()

set(URIPARSER_BUILT ON)


