# sample invoker - include to make sure it compiles
set(USCXML_INVOKERS "sample ${USCXML_INVOKERS}")
file(GLOB_RECURSE SAMPLE_INVOKER
	sample/*.cpp
	sample/*.h
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

set(USCXML_INVOKERS "dirmon ${USCXML_INVOKERS}")
file(GLOB_RECURSE DIRMON_INVOKER
	filesystem/dirmon/*.cpp
	filesystem/dirmon/*.h
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

# DirMon invoker to watch for filesystem changes

set(USCXML_INVOKERS "xmlbridge ${USCXML_INVOKERS}")
file(GLOB_RECURSE XMLBRIDGE_INVOKER
	system/XmlBridgeInvoker.cpp
	system/XmlBridgeInvoker.h
)
source_group("Invoker\\xmlbridge" FILES ${XMLBRIDGE_INVOKER})
if (BUILD_AS_PLUGINS)
	add_library(
		invoker_xmlbridge SHARED 
		${XMLBRIDGE_INVOKER})
	target_link_libraries(invoker_xmlbridge uscxml)
	set_target_properties(invoker_xmlbridge PROPERTIES FOLDER "Plugin Invoker")
else()
	list (APPEND USCXML_FILES ${XMLBRIDGE_INVOKER})
endif()

# Location invoker to watch for proximity to GPS coordinates

file(GLOB_RECURSE LOCATION_INVOKER
	location/*.cpp
	location/*.h
)
source_group("Invoker\\location" FILES ${LOCATION_INVOKER})
if (BUILD_AS_PLUGINS)
	add_library(
		invoker_location SHARED 
		${LOCATION_INVOKER})
	target_link_libraries(invoker_location uscxml)
	set_target_properties(invoker_location PROPERTIES FOLDER "Plugin Invoker")
else()
	list (APPEND USCXML_FILES ${LOCATION_INVOKER})
endif()


# XHTML invoker

set(USCXML_INVOKERS "xhtml ${USCXML_INVOKERS}")
file(GLOB_RECURSE XHTML_INVOKER
	xhtml/*.cpp
	xhtml/*.h
)
source_group("Invoker\\xhtml" FILES ${XHTML_INVOKER})
if (BUILD_AS_PLUGINS)
	add_library(
		invoker_xhtml SHARED 
		${XHTML_INVOKER})
	target_link_libraries(invoker_xhtml uscxml)
	set_target_properties(invoker_xhtml PROPERTIES FOLDER "Plugin Invoker")
else()
	list (APPEND USCXML_FILES ${XHTML_INVOKER})
endif()


# System invoker to open a native command

file(GLOB_RECURSE SYSTEM_INVOKER
	system/*.cpp
	system/*.h
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

if (SQLITE3_FOUND)
	file(GLOB_RECURSE SQLITE3_INVOKER
		sqlite3/*.cpp
		sqlite3/*.h
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

if (FFMPEG_FOUND)
	set(USCXML_INVOKERS "ffmpeg ${USCXML_INVOKERS}")
	file(GLOB_RECURSE FFMPEG_INVOKER
		ffmpeg/*.cpp
		ffmpeg/*.h
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


# instant messaging invoker

if (LIBPURPLE_FOUND)
	set(USCXML_INVOKERS "im ${USCXML_INVOKERS}")
	file(GLOB_RECURSE LIBPURPLE_INVOKER
		im/*.cpp
		im/*.h
	)
	source_group("Invoker\\im" FILES ${LIBPURPLE_INVOKER})
	if (BUILD_AS_PLUGINS)
		add_library(
			invoker_im SHARED 
			${LIBPURPLE_INVOKER})
		target_link_libraries(invoker_im uscxml)
		set_target_properties(invoker_im PROPERTIES FOLDER "Plugin Invoker")
	else()
		list (APPEND USCXML_FILES ${LIBPURPLE_INVOKER})
	endif()
endif()


# calendar invoker

if (LIBICAL_FOUND)
	set(USCXML_INVOKERS "calendar ${USCXML_INVOKERS}")
	file(GLOB_RECURSE CALENDAR_INVOKER
		calendar/*.cpp
		calendar/*.h
	)
	source_group("Invoker\\calendar" FILES ${CALENDAR_INVOKER})
	if (BUILD_AS_PLUGINS)
		add_library(
			invoker_calendar SHARED 
			${CALENDAR_INVOKER})
		target_link_libraries(invoker_calendar uscxml)
		set_target_properties(invoker_calendar PROPERTIES FOLDER "Plugin Invoker")
	else()
		list (APPEND USCXML_FILES ${CALENDAR_INVOKER})
	endif()
endif()


# location invoker

if (CORELOCATION_LIBRARY AND OFF)
	set(USCXML_INVOKERS "location ${USCXML_INVOKERS}")
	file(GLOB_RECURSE LOCATION_INVOKER
		location/CoreLocation/*.cpp
		location/CoreLocation/*.mm
		location/CoreLocation/*.h
	)
	source_group("Invoker\\location" FILES ${LOCATION_INVOKER})
	if (BUILD_AS_PLUGINS)
		add_library(
			invoker_location SHARED 
			${LOCATION_INVOKER})
		target_link_libraries(invoker_location uscxml)
		set_target_properties(invoker_location PROPERTIES FOLDER "Plugin Invoker")
	else()
		list (APPEND USCXML_FILES ${LOCATION_INVOKER})
	endif()
endif()


# UMUNDO invoker 

if (UMUNDO_FOUND)
	set(USCXML_INVOKERS "umundo ${USCXML_INVOKERS}")
	file(GLOB_RECURSE UMUNDO_INVOKER 
		umundo/*.cpp 
		umundo/*.cc 
		umundo/*.h)
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
	endif()
endif()


# USCXML invoker 

set(USCXML_INVOKERS "scxml ${USCXML_INVOKERS}")
file(GLOB_RECURSE USCXML_INVOKER 
	scxml/*.cpp 
	scxml/*.h)
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

set(USCXML_INVOKERS "httpservlet ${USCXML_INVOKERS}")
file(GLOB_RECURSE HTTPSERVLET_INVOKER 
	http/*.cpp 
	http/*.h)
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

set(USCXML_INVOKERS "heartbeat ${USCXML_INVOKERS}")
file(GLOB_RECURSE HEARTBEAT_INVOKER
	heartbeat/*.cpp
	heartbeat/*.h
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
if (OPENSCENEGRAPH_FOUND AND OPENGL_FOUND)
	set(USCXML_INVOKERS "scenegraph ${USCXML_INVOKERS}")
	file(GLOB OPENSCENEGRAPH_INVOKER 
		graphics/openscenegraph/*.cpp 
		graphics/openscenegraph/*.h)
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
	endif()

	set(USCXML_INVOKERS "osgvonvert ${USCXML_INVOKERS}")
	file(GLOB OPENSCENEGRAPH_CONVERTER_INVOKER 
		graphics/openscenegraph/converter/*.cpp 
		graphics/openscenegraph/converter/*.h)
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
	endif()
endif()


# OpenAL modality components

if (OPENAL_FOUND AND (LIBSNDFILE_FOUND OR AUDIOTOOLBOX_FOUND))
	set(USCXML_INVOKERS "openal ${USCXML_INVOKERS}")
	file(GLOB_RECURSE OPENAL_INVOKER 
		audio/OpenAL*.cpp 
		audio/OpenAL*.h)
	if (LIBSNDFILE_FOUND)
		file(GLOB_RECURSE LIBSNDFILE_WRAPPER 
			audio/LibSoundFile*.cpp 
			audio/LibSoundFile*.h)
		LIST(APPEND OPENAL_INVOKER ${LIBSNDFILE_WRAPPER})
	elseif(AUDIOTOOLBOX_FOUND)
		file(GLOB_RECURSE AUDIOTOOLBOX_WRAPPER 
			audio/AudioToolbox*.mm 
			audio/AudioToolbox*.h)
		LIST(APPEND OPENAL_INVOKER ${AUDIOTOOLBOX_WRAPPER})
	endif()
	source_group("Invoker\\audio" FILES ${OPENAL_INVOKER})
#	message("MILES_INVOKER ${MILES_INVOKER}")

	if (BUILD_AS_PLUGINS)
		add_library(
			invoker_openal SHARED 
			${OPENAL_INVOKER})
		target_link_libraries(invoker_openal 
			${OPENAL_LIBRARY}
			uscxml)
		set_target_properties(invoker_openal PROPERTIES FOLDER "Plugin Invoker")
	else()
  	list (APPEND USCXML_FILES ${OPENAL_INVOKER})
	endif()
endif()


# MILES modality components

if (MILES_FOUND)
	set(USCXML_INVOKERS "miles ${USCXML_INVOKERS}")
  file(GLOB_RECURSE MILES_INVOKER 
		miles/*.cpp 
		miles/*.h)
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
	endif()
endif()


# VoiceXML modality components

if (UMUNDO_FOUND)
	set(USCXML_INVOKERS "vxml ${USCXML_INVOKERS}")
	file(GLOB_RECURSE VXML_INVOKER
		vxml/*.cpp
		vxml/*.h
	)
	source_group("Invoker\\voicexml" FILES ${VXML_INVOKER})
	if (BUILD_AS_PLUGINS)
		add_library(
			invoker_voicexml SHARED 
			${VXML_INVOKER})
		target_link_libraries(invoker_voicexml uscxml)
		set_target_properties(invoker_voicexml PROPERTIES FOLDER "Plugin Invoker")
	else()
		list (APPEND USCXML_FILES ${VXML_INVOKER})
	endif()
endif()

set(USCXML_INCLUDE_DIRS ${USCXML_INCLUDE_DIRS} PARENT_SCOPE)
set(USCXML_FILES ${USCXML_FILES} PARENT_SCOPE)
set(USCXML_INVOKERS ${USCXML_INVOKERS} PARENT_SCOPE)
