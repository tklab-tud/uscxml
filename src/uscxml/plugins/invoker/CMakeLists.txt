# sample invoker - include to make sure it compiles
file(GLOB_RECURSE SAMPLE_INVOKER
	src/uscxml/plugins/invoker/sample/*.cpp
	src/uscxml/plugins/invoker/sample/*.h
)
source_group("Invoker\\sample" FILES ${SAMPLE_INVOKER})
if (BUILD_AS_PLUGINS)
	add_library(
		invoker_sample SHARED 
		${SAMPLE_INVOKER})
	target_link_libraries(invoker_sample uscxml)
	set_target_properties(invoker_sample PROPERTIES FOLDER "Plugin Invoker")
else()
	list (APPEND USCXML_FILES ${SAMPLE_INVOKER})
endif()


# DirMon invoker to watch for filesystem changes

file(GLOB_RECURSE DIRMON_INVOKER
	src/uscxml/plugins/invoker/filesystem/dirmon/*.cpp
	src/uscxml/plugins/invoker/filesystem/dirmon/*.h
)
source_group("Invoker\\dirmon" FILES ${DIRMON_INVOKER})
if (BUILD_AS_PLUGINS)
	add_library(
		invoker_dirmon SHARED 
		${DIRMON_INVOKER})
	target_link_libraries(invoker_dirmon uscxml)
	set_target_properties(invoker_dirmon PROPERTIES FOLDER "Plugin Invoker")
else()
	list (APPEND USCXML_FILES ${DIRMON_INVOKER})
endif()


# System invoker to open a native command

file(GLOB_RECURSE SYSTEM_INVOKER
	src/uscxml/plugins/invoker/system/*.cpp
	src/uscxml/plugins/invoker/system/*.h
)
source_group("Invoker\\system" FILES ${SYSTEM_INVOKER})
if (BUILD_AS_PLUGINS)
	add_library(
		invoker_system SHARED 
		${SYSTEM_INVOKER})
	target_link_libraries(invoker_system uscxml)
	set_target_properties(invoker_system PROPERTIES FOLDER "Plugin Invoker")
else()
	list (APPEND USCXML_FILES ${SYSTEM_INVOKER})
endif()


# SQLite3 SQL Invoker

find_package(Sqlite3)
if (SQLITE3_FOUND)
	file(GLOB_RECURSE SQLITE3_INVOKER
		src/uscxml/plugins/invoker/sqlite3/*.cpp
		src/uscxml/plugins/invoker/sqlite3/*.h
	)
	source_group("Invoker\\sqlite" FILES ${SQLITE3_INVOKER})
	if (BUILD_AS_PLUGINS)
		add_library(
			invoker_sqlite3 SHARED 
			${SQLITE3_INVOKER})
		target_link_libraries(invoker_sqlite3 uscxml)
		set_target_properties(invoker_sqlite3 PROPERTIES FOLDER "Plugin Invoker")
	else()
		list (APPEND USCXML_FILES ${SQLITE3_INVOKER})
	endif()
endif()


# ffmpeg invoker

find_package(FFMPEG)
if (FFMPEG_FOUND)
	list (APPEND USCXML_INCLUDE_DIRS ${FFMPEG_INCLUDE_DIR})		
	file(GLOB_RECURSE FFMPEG_INVOKER
		src/uscxml/plugins/invoker/ffmpeg/*.cpp
		src/uscxml/plugins/invoker/ffmpeg/*.h
	)
	source_group("Invoker\\ffmpeg" FILES ${FFMPEG_INVOKER})
	if (BUILD_AS_PLUGINS)
		add_library(
			invoker_ffmpeg SHARED 
			${FFMPEG_INVOKER})
		target_link_libraries(invoker_ffmpeg uscxml)
		set_target_properties(invoker_ffmpeg PROPERTIES FOLDER "Plugin Invoker")
	else()
		list (APPEND USCXML_FILES ${FFMPEG_INVOKER})
	endif()
endif()


# UMUNDO invoker 

if (WIN32)
	find_package(UMUNDO COMPONENTS convenience)
else()
	find_package(UMUNDO COMPONENTS rpc serial core)
endif()
if (UMUNDO_FOUND)
	list (APPEND USCXML_INCLUDE_DIRS ${UMUNDO_INCLUDE_DIR})
	file(GLOB_RECURSE UMUNDO_INVOKER 
		src/uscxml/plugins/invoker/umundo/*.cpp 
		src/uscxml/plugins/invoker/umundo/*.h)
	source_group("Invoker\\umundo" FILES ${UMUNDO_INVOKER})
	if (BUILD_AS_PLUGINS)
		add_library(
			invoker_umundo SHARED 
			${UMUNDO_INVOKER})
		target_link_libraries(invoker_umundo 
			uscxml
			${UMUNDO_LIBRARIES})
		set_target_properties(invoker_umundo PROPERTIES FOLDER "Plugin Invoker")
	else()
		list (APPEND USCXML_FILES ${UMUNDO_INVOKER})
		list (APPEND USCXML_OPT_LIBS ${UMUNDO_LIBRARIES})
	endif()
	add_definitions("-DUMUNDO_STATIC")
endif()


# USCXML invoker 

file(GLOB_RECURSE USCXML_INVOKER 
	src/uscxml/plugins/invoker/scxml/*.cpp 
	src/uscxml/plugins/invoker/scxml/*.h)
source_group("Invoker\\uscxml" FILES ${USCXML_INVOKER})
if (BUILD_AS_PLUGINS)
	add_library(
		invoker_uscxml SHARED 
		${USCXML_INVOKER})
	target_link_libraries(invoker_uscxml 
		uscxml)
		set_target_properties(invoker_uscxml PROPERTIES FOLDER "Plugin Invoker")
else()
	list (APPEND USCXML_FILES ${USCXML_INVOKER})
endif()


# HTTP server invoker 

file(GLOB_RECURSE HTTPSERVLET_INVOKER 
	src/uscxml/plugins/invoker/http/*.cpp 
	src/uscxml/plugins/invoker/http/*.h)
source_group("Invoker\\httpservlet" FILES ${HTTPSERVLET_INVOKER})
if (BUILD_AS_PLUGINS)
	add_library(
		invoker_httpserver SHARED 
		${HTTPSERVLET_INVOKER})
	target_link_libraries(invoker_httpserver 
		uscxml)
		set_target_properties(invoker_httpserver PROPERTIES FOLDER "Plugin Invoker")
else()
	list (APPEND USCXML_FILES ${HTTPSERVLET_INVOKER})
endif()


# Heartbeat invoker

file(GLOB_RECURSE HEARTBEAT_INVOKER
	src/uscxml/plugins/invoker/heartbeat/*.cpp
	src/uscxml/plugins/invoker/heartbeat/*.h
)
source_group("Invoker\\heartbeat" FILES ${HEARTBEAT_INVOKER})
if (BUILD_AS_PLUGINS)
	add_library(
		invoker_heartbeat SHARED 
		${HEARTBEAT_INVOKER})
	target_link_libraries(invoker_heartbeat uscxml)
	set_target_properties(invoker_heartbeat PROPERTIES FOLDER "Plugin Invoker")
else()
	list (APPEND USCXML_FILES ${HEARTBEAT_INVOKER})
endif()


# OpenSceneGraph invoker
if (UNIX)
	set(CMAKE_FIND_LIBRARY_SUFFIXES ${CMAKE_FIND_LIBRARY_SUFFIXES_ORIG}) # link dynamically!
elseif(WIN32)
	if (ENV{OSG_ROOT} STREQUAL "")
		set(ENV{OSG_ROOT} "C:/Program Files/OpenSceneGraph-3.0.1")
	endif()
endif()
find_package(OpenSceneGraph COMPONENTS osgViewer osgGA osgText osgFX osgManipulator osgDB osgUtil OpenThreads)
find_package(OpenGL)
if (OPENSCENEGRAPH_FOUND AND OPENGL_FOUND)	
	list (APPEND USCXML_INCLUDE_DIRS ${OPENSCENEGRAPH_INCLUDE_DIRS})
	list (APPEND USCXML_INCLUDE_DIRS ${OPENGL_INCLUDE_DIR})

	file(GLOB OPENSCENEGRAPH_INVOKER 
		src/uscxml/plugins/invoker/graphics/openscenegraph/*.cpp 
		src/uscxml/plugins/invoker/graphics/openscenegraph/*.h)
	source_group("Invoker\\scenegraph" FILES ${OPENSCENEGRAPH_INVOKER})

	if (BUILD_AS_PLUGINS)
		add_library(
			invoker_openscenegraph SHARED 
			${OPENSCENEGRAPH_INVOKER})
		target_link_libraries(invoker_openscenegraph
			${OPENSCENEGRAPH_LIBRARIES}
			${OPENGL_LIBRARIES}
			uscxml)
			set_target_properties(invoker_openscenegraph PROPERTIES FOLDER "Plugin Invoker")
	else()
		list (APPEND USCXML_FILES ${OPENSCENEGRAPH_INVOKER})
		list (APPEND USCXML_OPT_LIBS ${OPENSCENEGRAPH_LIBRARIES} ${OPENGL_LIBRARIES})
	endif()

	file(GLOB OPENSCENEGRAPH_CONVERTER_INVOKER 
		src/uscxml/plugins/invoker/graphics/openscenegraph/converter/*.cpp 
		src/uscxml/plugins/invoker/graphics/openscenegraph/converter/*.h)
	source_group("Invoker\\scenegraph\\convert" FILES ${OPENSCENEGRAPH_CONVERTER_INVOKER})

	if (BUILD_AS_PLUGINS)
		add_library(
			invoker_openscenegraph_convert SHARED 
			${OPENSCENEGRAPH_CONVERTER_INVOKER})
		target_link_libraries(invoker_openscenegraph_convert
			${OPENSCENEGRAPH_LIBRARIES}
			${OPENGL_LIBRARIES}
			uscxml)
			set_target_properties(invoker_openscenegraph_convert PROPERTIES FOLDER "Plugin Invoker")
	else()
		list (APPEND USCXML_FILES ${OPENSCENEGRAPH_CONVERTER_INVOKER})
		list (APPEND USCXML_OPT_LIBS ${OPENSCENEGRAPH_LIBRARIES} ${OPENGL_LIBRARIES})
	endif()

endif()
if (UNIX)
	set(CMAKE_FIND_LIBRARY_SUFFIXES .lib .a ${CMAKE_FIND_LIBRARY_SUFFIXES})
endif()


# MILES modality components

find_package(MILES)
if (MILES_FOUND AND OFF)
	list (APPEND USCXML_INCLUDE_DIRS ${MILES_INCLUDE_DIR})

	# openal is only needed for miles
	find_package(OpenAL REQUIRED)
#	find_package(JPEG REQUIRED)
	list (APPEND MILES_LIBRARIES "iconv")
	list (APPEND MILES_LIBRARIES ${JPEG_LIBRARIES})
	list (APPEND USCXML_INCLUDE_DIRS ${OPENAL_INCLUDE_DIR})

  file(GLOB_RECURSE MILES_INVOKER 
		src/uscxml/plugins/invoker/miles/*.cpp 
		src/uscxml/plugins/invoker/miles/*.h)
	source_group("Invoker\\miles" FILES ${MILES_INVOKER})
#	message("MILES_INVOKER ${MILES_INVOKER}")

	if (BUILD_AS_PLUGINS)
		add_library(
			invoker_miles SHARED 
			${MILES_INVOKER})
		target_link_libraries(invoker_miles 
			${MILES_LIBRARIES}
			${OPENAL_LIBRARY}
			uscxml)
		set_target_properties(invoker_miles PROPERTIES FOLDER "Plugin Invoker")
	else()
  	list (APPEND USCXML_FILES ${MILES_INVOKER})
  	list (APPEND USCXML_OPT_LIBS ${MILES_LIBRARIES})
		list (APPEND USCXML_OPT_LIBS ${OPENAL_LIBRARY})
	endif()
endif()

