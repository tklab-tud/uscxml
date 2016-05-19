# see: http://www.vtk.org/Wiki/CMake:CPackConfiguration

##############################################################################
# gather host-native libraries
##############################################################################

# these are all the host-native libraries
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
	# message("PLATFORM_LIB: ${PLATFORM_LIB}")
	install(FILES ${PLATFORM_LIB} DESTINATION lib COMPONENT library)
	list (APPEND USCXML_CPACK_COMPONENTS "library")
endforeach()

############################################################
# Header Files
############################################################

file(GLOB_RECURSE USCXML_HEADERS 
  ${PROJECT_SOURCE_DIR}/src/*.h 
	${PROJECT_SOURCE_DIR}/src/*.hpp
	${CMAKE_BINARY_DIR}/uscxml/)

INSTALL_HEADERS(HEADERS ${USCXML_HEADERS} COMPONENT headers)
list (APPEND USCXML_CPACK_COMPONENTS "headers")

# foreach(USCXML_HEADER ${USCXML_HEADERS})
# 	message("USCXML_HEADER: ${USCXML_HEADER}")
# endforeach()



########################################
# VBS wrappers
########################################

if (WIN32)
	install(
		FILES ${PROJECT_SOURCE_DIR}/apps/uscxml-browser.vbs
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


if (NOT CMAKE_CROSS_COMPILING)
	list (APPEND USCXML_CPACK_COMPONENTS "tools")
endif()
list (REMOVE_DUPLICATES USCXML_CPACK_COMPONENTS)

# message("USCXML_CPACK_COMPONENTS: ${USCXML_CPACK_COMPONENTS}")

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
		" ;uSCXML SDK"
		"bin\\\\uscxml-browser.vbs;uSCXML Browser")

endif()

set(CPACK_PACKAGE_NAME "uscxml")
set(CPACK_PACKAGE_VENDOR "Telecooperation Group - TU Darmstadt")
set(CPACK_PACKAGE_CONTACT "radomski@tk.tu-darmstadt.de")
set(CPACK_PACKAGE_DESCRIPTION_SUMMARY "USCXML - state-chart interpreter")
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
# set(CPACK_DEBIAN_PACKAGE_DEPENDS "libcurl4-openssl, libxml2")
# set(CPACK_DEBIAN_PACKAGE_RECOMMENDS "swig2.0, protobuf-compiler")

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
	set(CPACK_COMPONENT_TOOLS_DESCRIPTION "Command-line tools to debug and monitor a uSCXML network.")
endif()


list(FIND USCXML_CPACK_COMPONENTS "docs" FOUND_ITEM)
if (FOUND_ITEM GREATER -1)
	set(CPACK_COMPONENT_DOCS_DISPLAY_NAME "Documentation")
	set(CPACK_COMPONENT_DOCS_DESCRIPTION "Auto-generated documentation.")
endif()


list(FIND USCXML_CPACK_COMPONENTS "library" FOUND_ITEM)
if (FOUND_ITEM GREATER -1)
	# define header description here as well
	set(CPACK_COMPONENT_HEADERS_DISPLAY_NAME "C++ headers ")
	set(CPACK_COMPONENT_HEADERS_DESCRIPTION "C++ header files for uSCXML and all its components.")
	set(CPACK_COMPONENT_HEADERS_GROUP "Development")

	set(CPACK_COMPONENT_LIBRARY_DISPLAY_NAME "C++ uSCXML libraries")
	set(CPACK_COMPONENT_LIBRARY_DESCRIPTION "Static libraries of the uSCXML components for C++ development.")
	set(CPACK_COMPONENT_LIBRARY_GROUP "Development")
	set(CPACK_COMPONENT_LIBRARY_DEPENDS headers)
	set(CPACK_COMPONENT_LIBRARY_DEPENDS libraryPrebuilt)
endif()

set(CPACK_COMPONENT_GROUP_DEVELOPMENT_DESCRIPTION "Libraries and Headers for uSCXML.")
