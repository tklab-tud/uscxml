# see http://www.kitware.com/products/html/BuildingExternalProjectsWithCMake2.8.html
# see http://tools.cinemapub.be/opendcp/opendcp-0.19-src/contrib/CMakeLists.txt

include(ExternalProject)
if(MSVC)
	set(VC_VERSION VC12)
	# see https://en.wikipedia.org/wiki/Visual_C%2B%2B

	# CMAKE_CXX_COMPILER_VERSION=16.0.40219.1
	# MSVC_VERSION=1600

	if (OFF)
	elseif(MSVC_VERSION LESS 1310)
		message(FATAL_ERROR "MSVC 7.1 or higher is required")
	elseif(MSVC_VERSION LESS 1400)
		set(VC_VERSION VC7.1)
	elseif(MSVC_VERSION LESS 1500)
		set(VC_VERSION VC8)
	elseif(MSVC_VERSION LESS 1600)
		set(VC_VERSION VC9)
	elseif(MSVC_VERSION LESS 1700)
		set(VC_VERSION VC10)
	elseif(MSVC_VERSION LESS 1800)
		set(VC_VERSION VC11)
	elseif (MSVC_VERSION LESS 1900)
		set(VC_VERSION VC12)
	else()
		# set(VC_PLATFORM /p:PlatformToolset=v140)
	endif()
	
	set(VSPROJECT_PATH "projects/Win32/${VC_VERSION}/xerces-all/XercesLib")
	
	set(XERCESC_BUILD_PATH_SUFFIX Win32)
	set(XERCESC_BUILD_PLATFORM Win32)
	if( CMAKE_SIZEOF_VOID_P EQUAL 8 )
		set(XERCESC_BUILD_PATH_SUFFIX Win64)
		set(XERCESC_BUILD_PLATFORM x64)
	endif()
	
	externalproject_add(xerces-c
		URL http://archive.apache.org/dist/xerces/c/3/sources/xerces-c-3.1.4.tar.gz
		URL_MD5 21bb097b711a513275379b59757cba4c
		BUILD_IN_SOURCE 1
		PREFIX ${CMAKE_BINARY_DIR}/deps/xerces-c
		CONFIGURE_COMMAND ""
		# BUILD_COMMAND cd ${VSPROJECT_PATH} && msbuild /p:Configuration=Static\ Release /p:Platform=x64 /p:RuntimeLibrary=MD_DynamicRelease ${VC_PLATFORM} /t:build XercesLib.vcxproj
		# INSTALL_COMMAND ${CMAKE_COMMAND} -E copy_directory Build/Win64/${VC_VERSION}/Static\ Release/ ${CMAKE_BINARY_DIR}/deps/xerces-c/lib/ && ${CMAKE_COMMAND} -E copy_directory src/ ${CMAKE_BINARY_DIR}/deps/xerces-c/include/
		BUILD_COMMAND cd ${VSPROJECT_PATH} && msbuild /p:Configuration=Release /p:Platform=${XERCESC_BUILD_PLATFORM} ${VC_PLATFORM} /t:build XercesLib.vcxproj
		INSTALL_COMMAND 
			${CMAKE_COMMAND} -E make_directory ${CMAKE_BINARY_DIR}/deps/xerces-c/lib &&
			${CMAKE_COMMAND} -E make_directory ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/Release &&
			${CMAKE_COMMAND} -E make_directory ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/Debug &&
			${CMAKE_COMMAND} -E copy_directory Build/${XERCESC_BUILD_PATH_SUFFIX}/${VC_VERSION}/Release/ ${CMAKE_BINARY_DIR}/deps/xerces-c/lib/ && 
			${CMAKE_COMMAND} -E copy ${CMAKE_BINARY_DIR}/deps/xerces-c/lib/xerces-c_3_1.dll ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/Release/ && 
			${CMAKE_COMMAND} -E copy ${CMAKE_BINARY_DIR}/deps/xerces-c/lib/xerces-c_3_1.dll ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/Debug/ && 
			${CMAKE_COMMAND} -E copy ${CMAKE_BINARY_DIR}/deps/xerces-c/lib/xerces-c_3_1.dll ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/ && 
			${CMAKE_COMMAND} -E copy_directory src/ ${CMAKE_BINARY_DIR}/deps/xerces-c/include/
		)
else()
	externalproject_add(xerces-c
		URL http://archive.apache.org/dist/xerces/c/3/sources/xerces-c-3.1.4.tar.gz
		URL_MD5 21bb097b711a513275379b59757cba4c
		BUILD_IN_SOURCE 0
		PREFIX ${CMAKE_BINARY_DIR}/deps/xerces-c
		CONFIGURE_COMMAND 
			"<SOURCE_DIR>/configure" 
			"--enable-static" 
			"--enable-shared"
			"--prefix=<INSTALL_DIR>"
	)
endif()	

# TODO: --with-curl=DIR 

set(XercesC_INCLUDE_DIRS ${CMAKE_BINARY_DIR}/deps/xerces-c/include)

if (APPLE)
	set(XercesC_LIBRARIES ${CMAKE_BINARY_DIR}/deps/xerces-c/lib/libxerces-c.dylib)
elseif(UNIX)
	set(XercesC_LIBRARIES ${CMAKE_BINARY_DIR}/deps/xerces-c/lib/libxerces-c.so)
elseif(WIN32)
	# set(XercesC_LIBRARIES ${CMAKE_BINARY_DIR}/deps/xerces-c/lib/xerces-c_static_3.lib)
	set(XercesC_LIBRARIES ${CMAKE_BINARY_DIR}/deps/xerces-c/lib/xerces-c_3.lib)
else()
	message(FATAL_ERROR "Unknown platform!")
endif()

SET(XercesC_BUILT ON)
