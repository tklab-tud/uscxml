include(ExternalProject)

if (WIN32)
	set(URIPARSER_LIBNAME "uriparser.lib")
elseif(UNIX)
	set(URIPARSER_LIBNAME "liburiparser.a")
endif()

if (UNIX)
	set(FORCE_FPIC "CFLAGS=-fPIC")

	externalproject_add(uriparser
		URL http://ufpr.dl.sourceforge.net/project/uriparser/Sources/0.8.4/uriparser-0.8.4.zip
		URL_MD5 a24c9ba0fd1a2c6c75d02859bf337cfa
		BUILD_IN_SOURCE 0
		PREFIX ${CMAKE_BINARY_DIR}/deps/uriparser
		CONFIGURE_COMMAND
			${FORCE_FPIC}
			"<SOURCE_DIR>/configure"
			"--disable-test"
			"--disable-doc"
			"--enable-static"
			"--prefix=<INSTALL_DIR>"
	)
elseif(MSVC)
		if( CMAKE_SIZEOF_VOID_P EQUAL 8 )
			# we cannot build 64bit with the given project -> patch
			set(VSPROJECT_PATH "win32/uriparser-vs2013")

			externalproject_add(uriparser
				URL http://ufpr.dl.sourceforge.net/project/uriparser/Sources/0.8.4/uriparser-0.8.4.zip
				URL_MD5 a24c9ba0fd1a2c6c75d02859bf337cfa
				BUILD_IN_SOURCE 1
				PREFIX ${CMAKE_BINARY_DIR}/deps/uriparser
				PATCH_COMMAND
					${CMAKE_COMMAND} -E make_directory <SOURCE_DIR>/win32/uriparser-vs2013/ &&
					${CMAKE_COMMAND} -E copy ${PROJECT_SOURCE_DIR}/contrib/patches/uriparser/uriparser.vcxproj <SOURCE_DIR>/win32/uriparser-vs2013/
				CONFIGURE_COMMAND ""
				BUILD_COMMAND cd ${VSPROJECT_PATH} && devenv /Upgrade uriparser.vcxproj && msbuild /p:Configuration=Release /p:Platform=x64 /t:build uriparser.vcxproj
				INSTALL_COMMAND ${CMAKE_COMMAND} -E make_directory ${CMAKE_BINARY_DIR}/deps/uriparser/lib && ${CMAKE_COMMAND} -E copy win32/uriparser.lib ${CMAKE_BINARY_DIR}/deps/uriparser/lib/ && ${CMAKE_COMMAND} -E copy_directory include ${CMAKE_BINARY_DIR}/deps/uriparser/include
			)
		else()
			set(VSPROJECT_PATH "win32/Visual_Studio_2005")

			externalproject_add(uriparser
				URL http://ufpr.dl.sourceforge.net/project/uriparser/Sources/0.8.4/uriparser-0.8.4.zip
				URL_MD5 a24c9ba0fd1a2c6c75d02859bf337cfa
				BUILD_IN_SOURCE 1
				PREFIX ${CMAKE_BINARY_DIR}/deps/uriparser
				CONFIGURE_COMMAND ""
				BUILD_COMMAND cd ${VSPROJECT_PATH} && devenv /Upgrade uriparser.vcproj && msbuild /p:Configuration=Release /p:Platform=Win32 /t:build uriparser.vcxproj
				INSTALL_COMMAND ${CMAKE_COMMAND} -E make_directory ${CMAKE_BINARY_DIR}/deps/uriparser/lib && ${CMAKE_COMMAND} -E copy win32/uriparser.lib ${CMAKE_BINARY_DIR}/deps/uriparser/lib/ && ${CMAKE_COMMAND} -E copy_directory include ${CMAKE_BINARY_DIR}/deps/uriparser/include
			)
		endif()

else()
	externalproject_add(uriparser
		URL http://ufpr.dl.sourceforge.net/project/uriparser/Sources/0.8.4/uriparser-0.8.4.zip
		URL_MD5 a24c9ba0fd1a2c6c75d02859bf337cfa
		BUILD_IN_SOURCE 1
		PREFIX ${CMAKE_BINARY_DIR}/deps/uriparser
		PATCH_COMMAND
			${CMAKE_COMMAND} -E copy ${PROJECT_SOURCE_DIR}/contrib/patches/uriparser/CMakeLists.txt <SOURCE_DIR>
		INSTALL_COMMAND 
			${CMAKE_COMMAND} -E make_directory ${CMAKE_BINARY_DIR}/deps/uriparser/lib && 
			${CMAKE_COMMAND} -E copy ${URIPARSER_LIBNAME} ${CMAKE_BINARY_DIR}/deps/uriparser/lib/ && 
			${CMAKE_COMMAND} -E copy_directory include ${CMAKE_BINARY_DIR}/deps/uriparser/include
	)
endif()

#
#
# elseif(MINGW)
# 	# MinGW
#
# 	externalproject_add(uriparser
# 		URL http://ufpr.dl.sourceforge.net/project/uriparser/Sources/0.8.4/uriparser-0.8.4.zip
# 		URL_MD5 a24c9ba0fd1a2c6c75d02859bf337cfa
# 		BUILD_IN_SOURCE 1
# 		PREFIX ${CMAKE_BINARY_DIR}/deps/uriparser
# 		CONFIGURE_COMMAND ""
# 		BUILD_COMMAND
# 			cd win32/MinGW &&
# 			mingw32-make.exe
# 		INSTALL_COMMAND ${CMAKE_COMMAND} -E make_directory ${CMAKE_BINARY_DIR}/deps/uriparser/lib && ${CMAKE_COMMAND} -E copy win32/uriparser.lib ${CMAKE_BINARY_DIR}/deps/uriparser/lib/ && ${CMAKE_COMMAND} -E copy_directory include ${CMAKE_BINARY_DIR}/deps/uriparser/include
# 	)
#
# else ()
#
# endif()

set(URIPARSER_INCLUDE_DIR ${CMAKE_BINARY_DIR}/deps/uriparser/include)

if (UNIX)
	set(URIPARSER_LIBRARY ${CMAKE_BINARY_DIR}/deps/uriparser/lib/liburiparser.a)
elseif(WIN32)
	set(URIPARSER_LIBRARY ${CMAKE_BINARY_DIR}/deps/uriparser/lib/uriparser.lib)
else()
	message(FATAL_ERROR "Unknown platform!")
endif()

set(URIPARSER_BUILT ON)


