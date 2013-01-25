# see: http://www.vtk.org/Wiki/CMake:CPackConfiguration

########################################################################################
# gather host-native libraries
################################################################################

# these are all the host-native libraries plus
file(GLOB_RECURSE PLATFORM_LIBS
	${CMAKE_LIBRARY_OUTPUT_DIRECTORY}/*.a
	${CMAKE_LIBRARY_OUTPUT_DIRECTORY}/*.so
	${CMAKE_LIBRARY_OUTPUT_DIRECTORY}/*.lib
	${CMAKE_LIBRARY_OUTPUT_DIRECTORY}/*.dylib
	${CMAKE_LIBRARY_OUTPUT_DIRECTORY}/*.jnilib
	${CMAKE_LIBRARY_OUTPUT_DIRECTORY}/*.dll
	${CMAKE_LIBRARY_OUTPUT_DIRECTORY}/*.pdb
#	${CMAKE_LIBRARY_OUTPUT_DIRECTORY}/*.exp
)

# sort host-native libraries into installation components
foreach(PLATFORM_LIB ${PLATFORM_LIBS})
#	message("PLATFORM_LIB: ${PLATFORM_LIB}")
	if (PLATFORM_LIB MATCHES ".*Native.*")
		install(FILES ${PLATFORM_LIB} DESTINATION lib COMPONENT librarySwig)
		list (APPEND USCXML_CPACK_COMPONENTS "librarySwig")
	elseif (PLATFORM_LIB MATCHES ".*uscxmlCSharp.*")
		install(FILES ${PLATFORM_LIB} DESTINATION share/uscxml/lib COMPONENT librarySwig)
		list (APPEND USCXML_CPACK_COMPONENTS "library")
	elseif (PLATFORM_LIB MATCHES ".*uscxml.*")
		install(FILES ${PLATFORM_LIB} DESTINATION lib COMPONENT library)
		list (APPEND USCXML_CPACK_COMPONENTS "library")
	else()
		message(STATUS "PACKAGE RELEASE UNK ${PLATFORM_LIB} - not packaging")
	endif()
endforeach()

########################################
# Pre-built libraries for host platform
########################################

# do follow symlinks with GLOB_RECURSE
#cmake_policy(SET CMP0009 OLD)

file(GLOB_RECURSE PREBUILT_LIBS FOLLOW_SYMLINKS
	${USCXML_PREBUILT_LIBRARY_PATH}/lib/*.a
	${USCXML_PREBUILT_LIBRARY_PATH}/lib/*.so
	${USCXML_PREBUILT_LIBRARY_PATH}/lib/*.dylib
	${USCXML_PREBUILT_LIBRARY_PATH}/lib/*.lib
	${USCXML_PREBUILT_LIBRARY_PATH}/lib/*.dll
	${USCXML_PREBUILT_LIBRARY_PATH}/lib/*.pdb
)

#message("USCXML_PREBUILT_LIBRARY_PATH: ${USCXML_PREBUILT_LIBRARY_PATH}")

foreach(PREBUILT_LIB ${PREBUILT_LIBS})
#	message("PREBUILT_LIB: ${PREBUILT_LIB}")
	# string(REGEX MATCH "prebuilt/[^//]+/[^//]+" CURR_PLATFORM ${PREBUILT_LIB})
	# message("CURR_PLATFORM: ${CURR_PLATFORM}")
	# install(FILES ${PREBUILT_LIB} DESTINATION share/uscxml/${CURR_PLATFORM} COMPONENT libraryPrebuilt)
	install(FILES ${PREBUILT_LIB} DESTINATION share/uscxml/deps COMPONENT libraryPrebuilt)
	list (APPEND USCXML_CPACK_COMPONENTS "libraryPrebuilt")
endforeach()


########################################
# VBS wrappers
########################################

if (WIN32)
	install(
		FILES ${PROJECT_SOURCE_DIR}/apps/mmi-browser.vbs
		DESTINATION bin 
		COMPONENT tools
		PERMISSIONS WORLD_EXECUTE OWNER_EXECUTE GROUP_EXECUTE OWNER_WRITE OWNER_READ GROUP_READ WORLD_READ # 755
	)
endif()

########################################
# Include documentation
########################################

# file(GLOB_RECURSE HTML_DOCS ${PROJECT_SOURCE_DIR}/docs/html/*)
# foreach(HTML_DOC ${HTML_DOCS})
# 	STRING(REGEX REPLACE "${PROJECT_SOURCE_DIR}/" "" HTML_PATH ${HTML_DOC})
# 	STRING(REGEX MATCH "(.*)[/\\]" HTML_PATH ${HTML_PATH})
# 	install(FILES ${HTML_DOC} DESTINATION share/uscxml/${HTML_PATH} COMPONENT docs)
# 	list (APPEND USCXML_CPACK_COMPONENTS "docs")
# #	message(STATUS ${HTML_PATH})
# endforeach()

########################################
# CMake Modules for clients
########################################

# install(FILES ${PROJECT_SOURCE_DIR}/contrib/cmake/FindUSCXML.cmake DESTINATION share/uscxml/cmake COMPONENT library)
# install(FILES ${PROJECT_SOURCE_DIR}/contrib/cmake/UseUSCXML.cmake DESTINATION share/uscxml/cmake COMPONENT library)

########################################
# Target languages
########################################

GET_TARGET_PROPERTY(USCXMLNATIVEJAVA_LOCATION USCXMLNativeJava LOCATION)
if (USCXMLNATIVEJAVA_LOCATION)
	if (DIST_PREPARE)
		if (EXISTS "${PROJECT_SOURCE_DIR}/package/uscxml.jar")
			install(FILES ${PROJECT_SOURCE_DIR}/package/uscxml.jar DESTINATION share/uscxml/java COMPONENT librarySwig)
		endif()
	else()
		if (EXISTS "${CMAKE_LIBRARY_OUTPUT_DIRECTORY}/uscxml.jar")
			install(FILES ${CMAKE_LIBRARY_OUTPUT_DIRECTORY}/uscxml.jar DESTINATION share/uscxml/java COMPONENT librarySwig)
		endif()
	endif()
	list (APPEND USCXML_CPACK_COMPONENTS "librarySwig")
endif()

# The CSharp bindings are already picked up as a host-native dll above
GET_TARGET_PROPERTY(USCXMLNATIVECSHARP_LOCATION USCXMLNativeCSharp LOCATION)
# if (USCXMLNATIVECSHARP_LOCATION)
# 	install(FILES ${CMAKE_LIBRARY_OUTPUT_DIRECTORY}/uscxmlCSharp.dll DESTINATION share/uscxml/lib COMPONENT librarySwig)
# 	list (APPEND USCXML_CPACK_COMPONENTS "librarySwig")
# endif()


################################################################################
# Cross Compiled binaries
################################################################################

########################################
# Android
########################################

file(GLOB_RECURSE ANDROID_LIBS ${PROJECT_SOURCE_DIR}/package/cross-compiled/android*/*)
foreach(ANDROID_LIB ${ANDROID_LIBS})
	# do not pack static libraries
#	if (NOT ANDROID_LIB MATCHES ".*\\.a" AND NOT ANDROID_LIB MATCHES "\\..*")
	if (NOT ANDROID_LIB MATCHES ".*\\.a")
		# remove weird double slashes
		STRING(REGEX REPLACE "//" "/" ANDROID_LIB ${ANDROID_LIB})
		# take relative path
		STRING(REGEX REPLACE "${PROJECT_SOURCE_DIR}/package/cross-compiled/" "" ANDROID_PATH ${ANDROID_LIB})
    # only take first two path elements
		STRING(REGEX MATCH "[^/]*/[^/]*" ANDROID_PATH ${ANDROID_PATH})
		# but remove USCXML.jar from path in any case
		STRING(REGEX REPLACE "/uscxml.jar" "" ANDROID_PATH ${ANDROID_PATH})
    # message(STATUS "ANDROID_PATH: ${ANDROID_PATH}")
    # message(STATUS "ANDROID_LIB: ${ANDROID_LIB}")
		install(FILES ${ANDROID_LIB} DESTINATION share/uscxml/${ANDROID_PATH} COMPONENT libraryAndroid)
		list (APPEND USCXML_CPACK_COMPONENTS "libraryAndroid")
	endif()
endforeach()

# list(FIND USCXML_CPACK_COMPONENTS "libraryAndroid" FOUND_ITEM)
# if (FOUND_ITEM GREATER -1)
# 	file(GLOB_RECURSE ANDROID_PREBUILT_LIBS ${PROJECT_SOURCE_DIR}/contrib/prebuilt/android*/*)
# 	foreach(ANDROID_PREBUILT_LIB ${ANDROID_PREBUILT_LIBS})
# 		STRING(REGEX REPLACE "//" "/" ANDROID_PREBUILT_LIB ${ANDROID_PREBUILT_LIB})
# 		STRING(REGEX MATCH "prebuilt/[^//]+/[^//]+" ANDROID_PLATFORM ${ANDROID_PREBUILT_LIB})
# 		message("ANDROID_PREBUILT_LIB: ${ANDROID_PREBUILT_LIB}")
# 		message("ANDROID_PLATFORM: ${ANDROID_PLATFORM}")
# 		install(FILES ${ANDROID_PREBUILT_LIB} DESTINATION share/uscxml/${ANDROID_PLATFORM} COMPONENT libraryPrebuilt)
# 	endforeach()
# endif()

########################################
# iOS
########################################
if (APPLE)
	file(GLOB_RECURSE IOS_LIBS ${PROJECT_SOURCE_DIR}/package/cross-compiled/ios*/*.ios*)
	foreach(IOS_LIB ${IOS_LIBS})
		# match ios-5.0
		STRING(REGEX REPLACE "//" "/" IOS_LIB ${IOS_LIB})
		STRING(REGEX REPLACE "${PROJECT_SOURCE_DIR}/package/cross-compiled/" "" IOS_PATH ${IOS_LIB})
		STRING(REGEX MATCH "[^/]*" IOS_PATH ${IOS_PATH})
		# message(STATUS "IOS_LIB:  ${IOS_LIB}")
		# message(STATUS "IOS_PATH: ${IOS_PATH}")
		install(FILES ${IOS_LIB} DESTINATION share/uscxml/${IOS_PATH} COMPONENT libraryIOS)
		list (APPEND USCXML_CPACK_COMPONENTS "libraryIOS")
	endforeach()

	list(FIND USCXML_CPACK_COMPONENTS "libraryIOS" FOUND_ITEM)
	if (FOUND_ITEM GREATER -1)
		file(GLOB_RECURSE IOS_PREBUILT_LIBS ${PROJECT_SOURCE_DIR}/contrib/prebuilt/ios*/*.a)
		foreach(IOS_PREBUILT_LIB ${IOS_PREBUILT_LIBS})
			if(NOT EXISTS "${IOS_PREBUILT_LIB}/")
				STRING(REGEX REPLACE "//" "/" IOS_PREBUILT_LIB ${IOS_PREBUILT_LIB})
				STRING(REGEX MATCH "ios/[^//]+" IOS_PLATFORM ${IOS_PREBUILT_LIB})
				# message("IOS_PLATFORM: ${IOS_PLATFORM}")
				# message("IOS_PREBUILT_LIB: ${IOS_PREBUILT_LIB}")
				install(FILES ${IOS_PREBUILT_LIB} DESTINATION share/uscxml/deps/${IOS_PLATFORM} COMPONENT libraryPrebuilt)
			endif()
		endforeach()
	endif()
endif()

################################################################################
# Sample projects
################################################################################

# USCXML-pingpong: XCode for iOS
if (APPLE)
	file(GLOB_RECURSE IOS_PINGPONG_SAMPLE ${PROJECT_SOURCE_DIR}/examples/ios/uscxml-pingpong*/*)
	foreach(IOS_PINGPONG_SAMPLE_FILE ${IOS_PINGPONG_SAMPLE})
		# strip root
		STRING(REGEX REPLACE "${PROJECT_SOURCE_DIR}/examples" "" REL_PATH ${IOS_PINGPONG_SAMPLE_FILE})
		get_filename_component(REL_PATH ${REL_PATH} PATH)
#		message("Installing ${IOS_PINGPONG_SAMPLE_FILE} in share/uscxml/samples/${REL_PATH}")
		install(FILES ${IOS_PINGPONG_SAMPLE_FILE} DESTINATION share/uscxml/samples/${REL_PATH} COMPONENT samples)
	endforeach()
	list (APPEND USCXML_CPACK_COMPONENTS "samples")
endif()

# USCXML-pingpong: Eclipse for Android
file(GLOB_RECURSE ANDROID_PINGPONG_SAMPLE ${PROJECT_SOURCE_DIR}/examples/android/*)
foreach(ANDROID_PINGPONG_SAMPLE_FILE ${ANDROID_PINGPONG_SAMPLE})
#	message("ANDROID_PINGPONG_SAMPLE_FILE: ${ANDROID_PINGPONG_SAMPLE_FILE}")
	STRING(REGEX REPLACE "${PROJECT_SOURCE_DIR}/examples" "" REL_PATH ${ANDROID_PINGPONG_SAMPLE_FILE})
	get_filename_component(REL_PATH ${REL_PATH} PATH)
	install(FILES ${ANDROID_PINGPONG_SAMPLE_FILE} DESTINATION share/uscxml/samples/${REL_PATH} COMPONENT samples)
endforeach()
list (APPEND USCXML_CPACK_COMPONENTS "samples")

# USCXML-pingpong: Visual Studio for CSharp
if (WIN32)
	file(GLOB_RECURSE CSHARP_PINGPONG_SAMPLE ${PROJECT_SOURCE_DIR}/examples/csharp/*)
	foreach(CSHARP_PINGPONG_SAMPLE_FILE ${CSHARP_PINGPONG_SAMPLE})
#		message("CSHARP_PINGPONG_SAMPLE_FILE: ${CSHARP_PINGPONG_SAMPLE_FILE}")
		STRING(REGEX REPLACE "${PROJECT_SOURCE_DIR}/examples" "" REL_PATH ${CSHARP_PINGPONG_SAMPLE_FILE})
		get_filename_component(REL_PATH ${REL_PATH} PATH)
		install(FILES ${CSHARP_PINGPONG_SAMPLE_FILE} DESTINATION share/uscxml/samples/${REL_PATH} COMPONENT samples)
	endforeach()
	list (APPEND USCXML_CPACK_COMPONENTS "samples")
endif()

# All the java samples
file(GLOB_RECURSE JAVA_SAMPLES ${PROJECT_SOURCE_DIR}/examples/java/*)
foreach(JAVA_SAMPLES_FILE ${JAVA_SAMPLES})
	STRING(REGEX REPLACE "${PROJECT_SOURCE_DIR}/examples" "" REL_PATH ${JAVA_SAMPLES_FILE})
	get_filename_component(REL_PATH ${REL_PATH} PATH)
	install(FILES ${JAVA_SAMPLES_FILE} DESTINATION share/uscxml/samples/${REL_PATH} COMPONENT samples)
endforeach()

# All the cpp samples
file(GLOB_RECURSE CPP_SAMPLES ${PROJECT_SOURCE_DIR}/examples/cpp/*)
foreach(CPP_SAMPLES_FILE ${CPP_SAMPLES})
	STRING(REGEX REPLACE "${PROJECT_SOURCE_DIR}/examples" "" REL_PATH ${CPP_SAMPLES_FILE})
	get_filename_component(REL_PATH ${REL_PATH} PATH)
	install(FILES ${CPP_SAMPLES_FILE} DESTINATION share/uscxml/samples/${REL_PATH} COMPONENT samples)
endforeach()

list (APPEND USCXML_CPACK_COMPONENTS "samples")

########################################
# Sample SCXML Files
########################################

file(GLOB_RECURSE SCXML_SAMPLES ${PROJECT_SOURCE_DIR}/test/samples/*)
foreach(SCXML_SAMPLE_FILE ${SCXML_SAMPLES})
	STRING(REGEX REPLACE "${PROJECT_SOURCE_DIR}/test/samples/" "" REL_PATH ${SCXML_SAMPLE_FILE})
	get_filename_component(REL_PATH ${REL_PATH} PATH)
#	message("Installing sample: share/uscxml/samples/${REL_PATH}")
	install(FILES ${SCXML_SAMPLE_FILE} DESTINATION share/uscxml/samples/${REL_PATH} COMPONENT samples)
endforeach()


########################################
# House keeping
########################################

list (APPEND USCXML_CPACK_COMPONENTS "headers")

if (NOT CMAKE_CROSS_COMPILING)
	list (APPEND USCXML_CPACK_COMPONENTS "tools")
endif()
list (REMOVE_DUPLICATES USCXML_CPACK_COMPONENTS)
#message("USCXML_CPACK_COMPONENTS: ${USCXML_CPACK_COMPONENTS}")

########################################
# Configure packagers
########################################

if (UNIX)
	if (APPLE)
		set(CPACK_GENERATOR "PackageMaker;TGZ")
	else()
		set(CPACK_GENERATOR "DEB;RPM;TGZ")
	endif()
	set(CPACK_PACKAGING_INSTALL_PREFIX "/usr/local")
endif()
if (WIN32)
	set(CPACK_GENERATOR "NSIS;ZIP")
	set(CPACK_PACKAGE_INSTALL_DIRECTORY "uscxml")
	# pairs of executables and labels for start menu
	set(CPACK_NSIS_MENU_LINKS
		" ;USCXML SDK"
		"bin\\\\mmi-browser.vbs;MMI Browser")

endif()

set(CPACK_PACKAGE_NAME "USCXML")
set(CPACK_PACKAGE_VENDOR "Telecooperation Group - TU Darmstadt")
set(CPACK_PACKAGE_CONTACT "radomski@tk.informatik.tu-darmstadt.de")
set(CPACK_PACKAGE_DESCRIPTION_SUMMARY "USCXML - publish/subscribe since 2012")
set(CPACK_PACKAGE_DESCRIPTION_FILE "${PROJECT_SOURCE_DIR}/installer/description.txt")
set(CPACK_RESOURCE_FILE_LICENSE "${PROJECT_SOURCE_DIR}/installer/license.txt")

set(CPACK_PACKAGE_VERSION "${USCXML_VERSION_MAJOR}.${USCXML_VERSION_MINOR}.${USCXML_VERSION_PATCH}")
set(CPACK_PACKAGE_VERSION_MAJOR ${USCXML_VERSION_MAJOR})
set(CPACK_PACKAGE_VERSION_MINOR ${USCXML_VERSION_MINOR})
set(CPACK_PACKAGE_VERSION_PATCH ${USCXML_VERSION_PATCH})

if (64BIT_HOST AND WIN32)
	set(CPACK_PACKAGE_FILE_NAME "${CMAKE_PROJECT_NAME}-${CMAKE_SYSTEM_NAME_LC}-${CMAKE_SYSTEM_PROCESSOR}_64-${CPACK_PACKAGE_VERSION}")
else()
	set(CPACK_PACKAGE_FILE_NAME "${CMAKE_PROJECT_NAME}-${CMAKE_SYSTEM_NAME_LC}-${CMAKE_SYSTEM_PROCESSOR}-${CPACK_PACKAGE_VERSION}")
endif()

###
# Configuration for NSIS installer on Win32
#
# pairs of executables and labels for start menu
#CPACK_PACKAGE_EXECUTABLES
set(CPACK_PACKAGE_INSTALL_REGISTRY_KEY "uscxml.telecooperation.tu-darmstadt")
if (WIN32)
	set(CPACK_PACKAGE_ICON "${PROJECT_SOURCE_DIR}\\\\installer\\\\nsis\\\\uscxml-logo.bmp")
else()
	set(CPACK_PACKAGE_ICON "${PROJECT_SOURCE_DIR}/installer/nsis/uscxml-logo.bmp")
endif()

###
# Configuration for PackageMaker on MacOSX
#
set(CPACK_RESOURCE_FILE_README "${PROJECT_SOURCE_DIR}/installer/packageMaker/readme.txt")
set(CPACK_RESOURCE_FILE_WELCOME "${PROJECT_SOURCE_DIR}/installer/packageMaker/welcome.txt")

###
# Configuration for debian packages
#
set(CPACK_DEBIAN_PACKAGE_NAME "uscxml")
set(CPACK_DEBIAN_PACKAGE_DEPENDS "libavahi-client3, libxml2")
set(CPACK_DEBIAN_PACKAGE_RECOMMENDS "swig2.0, protobuf-compiler")

###
# Configuration for RPM packages
#
set(CPACK_RPM_PACKAGE_NAME "uscxml")
set(CPACK_RPM_PACKAGE_LICENSE "Simplified BSD")


########################################
# Describe layout of package
########################################

set(CPACK_COMPONENTS_ALL
	${USCXML_CPACK_COMPONENTS}
)

###
# Description of components
#

list(FIND USCXML_CPACK_COMPONENTS "tools" FOUND_ITEM)
if (FOUND_ITEM GREATER -1)
	set(CPACK_COMPONENT_TOOLS_DISPLAY_NAME "Command-line Tools")
	set(CPACK_COMPONENT_TOOLS_DESCRIPTION "Command-line tools to debug and monitor a USCXML network.")
endif()

list(FIND USCXML_CPACK_COMPONENTS "samples" FOUND_ITEM)
if (FOUND_ITEM GREATER -1)
	set(CPACK_COMPONENT_SAMPLES_DISPLAY_NAME "IDE Templates and sample programs")
	set(CPACK_COMPONENT_SAMPLES_DESCRIPTION
  		"Templates for Xcode, Visual Studio and Eclipse with sample programs.")
endif()

list(FIND USCXML_CPACK_COMPONENTS "docs" FOUND_ITEM)
if (FOUND_ITEM GREATER -1)
	set(CPACK_COMPONENT_DOCS_DISPLAY_NAME "Documentation")
	set(CPACK_COMPONENT_DOCS_DESCRIPTION "Auto-generated documentation.")
endif()

list(FIND USCXML_CPACK_COMPONENTS "librarySwig" FOUND_ITEM)
if (FOUND_ITEM GREATER -1)
	set(CPACK_COMPONENT_LIBRARYSWIG_DISPLAY_NAME "Java interface")
	set(CPACK_COMPONENT_LIBRARYSWIG_DESCRIPTION "USCXML.core library wrapped for Java per native interfaces. This will install the actual library and the JAR archive.")
	set(CPACK_COMPONENT_LIBRARYSWIG_GROUP "Development")
endif()

list(FIND USCXML_CPACK_COMPONENTS "libraryPrebuilt" FOUND_ITEM)
if (FOUND_ITEM GREATER -1)
	set(CPACK_COMPONENT_LIBRARYPREBUILT_DISPLAY_NAME "C++ dependent libraries")
	set(CPACK_COMPONENT_LIBRARYPREBUILT_DESCRIPTION "Prebuilt libraries for this host and the cross-compile targets")
	set(CPACK_COMPONENT_LIBRARYPREBUILT_GROUP "Development")
endif()

list(FIND USCXML_CPACK_COMPONENTS "libraryAndroid" FOUND_ITEM)
if (FOUND_ITEM GREATER -1)
	set(CPACK_COMPONENT_LIBRARYANDROID_DISPLAY_NAME "Android libraries")
	set(CPACK_COMPONENT_LIBRARYANDROID_DESCRIPTION "USCXML.core cross compiled for Android devices.")
	set(CPACK_COMPONENT_LIBRARYANDROID_GROUP "Development")
endif()

list(FIND USCXML_CPACK_COMPONENTS "libraryIOS" FOUND_ITEM)
if (FOUND_ITEM GREATER -1)
	set(CPACK_COMPONENT_LIBRARYIOS_DISPLAY_NAME "iOS libraries")
	set(CPACK_COMPONENT_LIBRARYIOS_DESCRIPTION "USCXML.core cross compiled for iOS devices (universal libraries).")
	set(CPACK_COMPONENT_LIBRARYIOS_GROUP "Development")
	set(CPACK_COMPONENT_LIBRARYIOS_DEPENDS headers)
	set(CPACK_COMPONENT_LIBRARYIOS_DEPENDS libraryPrebuilt)
endif()

list(FIND USCXML_CPACK_COMPONENTS "library" FOUND_ITEM)
if (FOUND_ITEM GREATER -1)
	# define header description here as well
	set(CPACK_COMPONENT_HEADERS_DISPLAY_NAME "C++ headers ")
	set(CPACK_COMPONENT_HEADERS_DESCRIPTION "C++ header files for USCXML and all its components.")
	set(CPACK_COMPONENT_HEADERS_GROUP "Development")

	set(CPACK_COMPONENT_LIBRARY_DISPLAY_NAME "C++ USCXML libraries")
	set(CPACK_COMPONENT_LIBRARY_DESCRIPTION "Static libraries of the USCXML components for C++ development.")
	set(CPACK_COMPONENT_LIBRARY_GROUP "Development")
	set(CPACK_COMPONENT_LIBRARY_DEPENDS headers)
	set(CPACK_COMPONENT_LIBRARY_DEPENDS libraryPrebuilt)
endif()

set(CPACK_COMPONENT_GROUP_DEVELOPMENT_DESCRIPTION "Libraries and Headers for USCXML.")
