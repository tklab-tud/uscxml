# sample invoker - include to make sure it compiles
set(USCXML_INVOKERS "sample ${USCXML_INVOKERS}")
file(GLOB_RECURSE SAMPLE_INVOKER
	sample/*.cpp
	sample/*.h
)

if (BUILD_AS_PLUGINS)
	source_group("" FILES ${SAMPLE_INVOKER})
	add_library(
		invoker_sample SHARED 
		${SAMPLE_INVOKER}
		"../Plugins.cpp")
	target_link_libraries(invoker_sample uscxml)
	set_target_properties(invoker_sample PROPERTIES FOLDER "Plugin Invoker")
	set_target_properties(invoker_sample PROPERTIES COMPILE_FLAGS "-DPLUMA_EXPORTS")
	set_target_properties(invoker_sample PROPERTIES RUNTIME_OUTPUT_DIRECTORY "${OUTPUT_DIR}/lib")
else()
	list (APPEND USCXML_FILES ${SAMPLE_INVOKER})
endif()

# DirMon invoker to watch for filesystem changes

set(USCXML_INVOKERS "dirmon ${USCXML_INVOKERS}")
file(GLOB_RECURSE DIRMON_INVOKER
	filesystem/dirmon/*.cpp
	filesystem/dirmon/*.h
)
if (BUILD_AS_PLUGINS)
	source_group("" FILES ${DIRMON_INVOKER})
	add_library(
		invoker_dirmon SHARED 
		${DIRMON_INVOKER}
		"../Plugins.cpp")
	target_link_libraries(invoker_dirmon uscxml)
	set_target_properties(invoker_dirmon PROPERTIES FOLDER "Plugin Invoker")
	set_target_properties(invoker_dirmon PROPERTIES COMPILE_FLAGS "-DPLUMA_EXPORTS")
	set_target_properties(invoker_dirmon PROPERTIES RUNTIME_OUTPUT_DIRECTORY "${OUTPUT_DIR}/lib")
else()
	list (APPEND USCXML_FILES ${DIRMON_INVOKER})
endif()


# Location invoker to watch for proximity to GPS coordinates

# file(GLOB_RECURSE LOCATION_INVOKER
# 	location/*.cpp
# 	location/*.h
# )
# if (BUILD_AS_PLUGINS)
# 	source_group("" FILES ${LOCATION_INVOKER})
# 	add_library(
# 		invoker_location SHARED 
# 		${LOCATION_INVOKER}
# 		"../Plugins.cpp")
# 	target_link_libraries(invoker_location uscxml)
# 	set_target_properties(invoker_location PROPERTIES FOLDER "Plugin Invoker")
# else()
# 	list (APPEND USCXML_FILES ${LOCATION_INVOKER})
# endif()


# XHTML invoker

set(USCXML_INVOKERS "xhtml ${USCXML_INVOKERS}")
file(GLOB_RECURSE XHTML_INVOKER
	xhtml/*.cpp
	xhtml/*.h
)
if (BUILD_AS_PLUGINS)
	source_group("" FILES ${XHTML_INVOKER})
	add_library(
		invoker_xhtml SHARED 
		${XHTML_INVOKER}
		"../Plugins.cpp")
	target_link_libraries(invoker_xhtml uscxml)
	set_target_properties(invoker_xhtml PROPERTIES FOLDER "Plugin Invoker")
	set_target_properties(invoker_xhtml PROPERTIES COMPILE_FLAGS "-DPLUMA_EXPORTS")
	set_target_properties(invoker_xhtml PROPERTIES RUNTIME_OUTPUT_DIRECTORY "${OUTPUT_DIR}/lib")
else()
	list (APPEND USCXML_FILES ${XHTML_INVOKER})
endif()


# System invoker to open a native command

file(GLOB_RECURSE SYSTEM_INVOKER
	system/*.cpp
	system/*.h
)
if (BUILD_AS_PLUGINS)
	source_group("" FILES ${SYSTEM_INVOKER})
	add_library(
		invoker_system SHARED 
		${SYSTEM_INVOKER}
		"../Plugins.cpp")
	target_link_libraries(invoker_system uscxml)
	set_target_properties(invoker_system PROPERTIES FOLDER "Plugin Invoker")
	set_target_properties(invoker_system PROPERTIES COMPILE_FLAGS "-DPLUMA_EXPORTS")
	set_target_properties(invoker_system PROPERTIES RUNTIME_OUTPUT_DIRECTORY "${OUTPUT_DIR}/lib")
else()
	list (APPEND USCXML_FILES ${SYSTEM_INVOKER})
endif()


# expect invoker

if (EXPECT_FOUND AND TCL_FOUND)
	set(USCXML_INVOKERS "expect ${USCXML_INVOKERS}")
	file(GLOB_RECURSE EXPECT_INVOKER
		expect/*.cpp
		expect/*.h
	)
	if (BUILD_AS_PLUGINS)
		source_group("" FILES EXPECT_INVOKER)
		add_library(
			invoker_expect SHARED 
			${EXPECT_INVOKER}
			"../Plugins.cpp")
		target_link_libraries(invoker_expect uscxml ${EXPECT_LIBRARY} ${TCL_LIBRARY})
		set_target_properties(invoker_expect PROPERTIES FOLDER "Plugin Invoker")
		set_target_properties(invoker_expect PROPERTIES COMPILE_FLAGS "-DPLUMA_EXPORTS")
		set_target_properties(invoker_expect PROPERTIES RUNTIME_OUTPUT_DIRECTORY "${OUTPUT_DIR}/lib")
	else()
		list (APPEND USCXML_FILES ${EXPECT_INVOKER})
	endif()
endif()


# SMTP invoker via curl

if (CURL_HAS_SMTP)
	set(USCXML_INVOKERS "smtp ${USCXML_INVOKERS}")
	file(GLOB_RECURSE SMTP_INVOKER
		smtp/*.cpp
		smtp/*.h
	)
	if (BUILD_AS_PLUGINS)
		source_group("" FILES SMTP_INVOKER)
		add_library(
			invoker_smtp SHARED 
			${SMTP_INVOKER}
			"../Plugins.cpp")
		target_link_libraries(invoker_smtp uscxml)
		set_target_properties(invoker_smtp PROPERTIES FOLDER "Plugin Invoker")
		set_target_properties(invoker_smtp PROPERTIES COMPILE_FLAGS "-DPLUMA_EXPORTS")
		set_target_properties(invoker_smtp PROPERTIES RUNTIME_OUTPUT_DIRECTORY "${OUTPUT_DIR}/lib")
	else()
		list (APPEND USCXML_FILES ${SMTP_INVOKER})
	endif()
endif()


# IMAP invoker via curl

set(USCXML_INVOKERS "imap ${USCXML_INVOKERS}")
file(GLOB_RECURSE IMAP_INVOKER
	imap/*.cpp
	imap/*.h
)
if (BUILD_AS_PLUGINS)
	source_group("" FILES IMAP_INVOKER)
	add_library(
		invoker_imap SHARED 
		${IMAP_INVOKER}
		"../Plugins.cpp")
	target_link_libraries(invoker_imap uscxml)
	set_target_properties(invoker_imap PROPERTIES FOLDER "Plugin Invoker")
	set_target_properties(invoker_imap PROPERTIES COMPILE_FLAGS "-DPLUMA_EXPORTS")
	set_target_properties(invoker_imap PROPERTIES RUNTIME_OUTPUT_DIRECTORY "${OUTPUT_DIR}/lib")
else()
	list (APPEND USCXML_FILES ${IMAP_INVOKER})
endif()


# SQLite3 SQL Invoker

if (SQLITE3_FOUND)
	file(GLOB_RECURSE SQLITE3_INVOKER
		sqlite3/*.cpp
		sqlite3/*.h
	)
	if (BUILD_AS_PLUGINS)
		source_group("" FILES ${SQLITE3_INVOKER})
		add_library(
			invoker_sqlite3 SHARED 
			${SQLITE3_INVOKER}
			"../Plugins.cpp")
		target_link_libraries(invoker_sqlite3 uscxml)
		set_target_properties(invoker_sqlite3 PROPERTIES FOLDER "Plugin Invoker")
		set_target_properties(invoker_sqlite3 PROPERTIES COMPILE_FLAGS "-DPLUMA_EXPORTS")
		set_target_properties(invoker_sqlite3 PROPERTIES RUNTIME_OUTPUT_DIRECTORY "${OUTPUT_DIR}/lib")
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
	if (BUILD_AS_PLUGINS)
		source_group("" FILES ${FFMPEG_INVOKER})
		add_library(
			invoker_ffmpeg SHARED 
			${FFMPEG_INVOKER}
			"../Plugins.cpp")
		target_link_libraries(invoker_ffmpeg uscxml ${FFMPEG_LIBRARIES})
		set_target_properties(invoker_ffmpeg PROPERTIES FOLDER "Plugin Invoker")
		set_target_properties(invoker_ffmpeg PROPERTIES COMPILE_FLAGS "-DPLUMA_EXPORTS")
		set_target_properties(invoker_ffmpeg PROPERTIES RUNTIME_OUTPUT_DIRECTORY "${OUTPUT_DIR}/lib")
	else()
		list (APPEND USCXML_FILES ${FFMPEG_INVOKER})
	endif()
endif()


# instant messaging invoker

if (LIBPURPLE_FOUND)
	set(USCXML_INVOKERS "im ${USCXML_INVOKERS}")
	configure_file(${CMAKE_CURRENT_SOURCE_DIR}/im/IMConfig.h.in ${CMAKE_BINARY_DIR}/uscxml/IMConfig.h)
	
	file(GLOB_RECURSE LIBPURPLE_INVOKER
		im/*.cpp
		im/*.h
	)
	
	if (BUILD_AS_PLUGINS)
		source_group("" FILES ${LIBPURPLE_INVOKER})
		add_library(
			invoker_im SHARED 
			${LIBPURPLE_INVOKER}
			"../Plugins.cpp")
		target_link_libraries(invoker_im uscxml ${LIBPURPLE_LIBRARY} ${GLIB2_LIBRARIES} ${ICONV_LIBRARIES})
		set_target_properties(invoker_im PROPERTIES FOLDER "Plugin Invoker")
		set_target_properties(invoker_im PROPERTIES COMPILE_FLAGS "-DPLUMA_EXPORTS")
		set_target_properties(invoker_im PROPERTIES RUNTIME_OUTPUT_DIRECTORY "${OUTPUT_DIR}/lib")
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
	if (BUILD_AS_PLUGINS)
		source_group("" FILES ${CALENDAR_INVOKER})
		add_library(
			invoker_calendar SHARED 
			${CALENDAR_INVOKER}
			"../Plugins.cpp")
		target_link_libraries(invoker_calendar uscxml ${LIBICAL_LIBRARIES})
		set_target_properties(invoker_calendar PROPERTIES FOLDER "Plugin Invoker")
		set_target_properties(invoker_calendar PROPERTIES COMPILE_FLAGS "-DPLUMA_EXPORTS")
		set_target_properties(invoker_calendar PROPERTIES RUNTIME_OUTPUT_DIRECTORY "${OUTPUT_DIR}/lib")
	else()
		list (APPEND USCXML_FILES ${CALENDAR_INVOKER})
	endif()
endif()


# webrtc invoker

if (LIBJINGLE_FOUND)
	set(USCXML_INVOKERS "webrtc ${USCXML_INVOKERS}")
	file(GLOB_RECURSE WEBRTC_INVOKER
		webrtc/*.cpp
		webrtc/*.h
	)
	if (BUILD_AS_PLUGINS)
		source_group("" FILES ${WEBRTC_INVOKER})
		add_library(
			invoker_webrtc SHARED 
			${WEBRTC_INVOKER}
			"../Plugins.cpp")
		target_link_libraries(invoker_webrtc uscxml ${LIBJINGLE_LIBRARIES})
		set_target_properties(invoker_webrtc PROPERTIES FOLDER "Plugin Invoker")
		set_target_properties(invoker_webrtc PROPERTIES COMPILE_FLAGS "-DPLUMA_EXPORTS")
		set_target_properties(invoker_webrtc PROPERTIES RUNTIME_OUTPUT_DIRECTORY "${OUTPUT_DIR}/lib")
	else()
		list (APPEND USCXML_FILES ${WEBRTC_INVOKER})
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
	if (BUILD_AS_PLUGINS)
		source_group("" FILES ${LOCATION_INVOKER})
		add_library(
			invoker_location SHARED 
			${LOCATION_INVOKER}
			"../Plugins.cpp")
		target_link_libraries(invoker_location uscxml)
		set_target_properties(invoker_location PROPERTIES FOLDER "Plugin Invoker")
		set_target_properties(invoker_location PROPERTIES COMPILE_FLAGS "-DPLUMA_EXPORTS")
		set_target_properties(invoker_location PROPERTIES RUNTIME_OUTPUT_DIRECTORY "${OUTPUT_DIR}/lib")
	else()
		list (APPEND USCXML_FILES ${LOCATION_INVOKER})
	endif()
endif()


# UMUNDO invoker 

if (UMUNDO_FOUND AND PROTOBUF_FOUND)
	set(USCXML_INVOKERS "umundo ${USCXML_INVOKERS}")
	set(UMUNDO_INVOKER 
		${CMAKE_CURRENT_SOURCE_DIR}/umundo/UmundoInvoker.cpp 
		${CMAKE_CURRENT_SOURCE_DIR}/umundo/UmundoInvoker.h
	)
	if (PROTOBUF_FOUND)
		list(APPEND UMUNDO_INVOKER
			${CMAKE_CURRENT_SOURCE_DIR}/umundo/JSON.pb.cc
			${CMAKE_CURRENT_SOURCE_DIR}/umundo/JSON.pb.h
		)
	endif()
	if (BUILD_AS_PLUGINS)
		source_group("" FILES ${UMUNDO_INVOKER})
#		message(FATAL_ERROR "UMUNDO_LIBRARIES: ${UMUNDO_LIBRARIES}")
		add_library(
			invoker_umundo SHARED 
			${UMUNDO_INVOKER}
			"../Plugins.cpp")
		target_link_libraries(invoker_umundo uscxml 
			${UMUNDO_LIBRARIES})
		if (PROTOBUF_FOUND)
			target_link_libraries(invoker_umundo
			optimized ${PROTOBUF_LIBRARY}
			debug ${PROTOBUF_LIBRARY_DEBUG})
		endif()
		set_target_properties(invoker_umundo PROPERTIES FOLDER "Plugin Invoker")
		set_target_properties(invoker_umundo PROPERTIES COMPILE_FLAGS "-DPLUMA_EXPORTS")
		set_target_properties(invoker_umundo PROPERTIES RUNTIME_OUTPUT_DIRECTORY "${OUTPUT_DIR}/lib")
	else()
		list (APPEND USCXML_FILES ${UMUNDO_INVOKER})
	endif()
endif()


# USCXML invoker 

set(USCXML_INVOKERS "scxml ${USCXML_INVOKERS}")
file(GLOB_RECURSE USCXML_INVOKER 
	scxml/*.cpp 
	scxml/*.h)
if (BUILD_AS_PLUGINS)
	source_group("" FILES ${USCXML_INVOKER})
	add_library(
		invoker_uscxml SHARED 
		${USCXML_INVOKER}
		"../Plugins.cpp")
	target_link_libraries(invoker_uscxml uscxml)
	set_target_properties(invoker_uscxml PROPERTIES FOLDER "Plugin Invoker")
	set_target_properties(invoker_uscxml PROPERTIES COMPILE_FLAGS "-DPLUMA_EXPORTS")
	set_target_properties(invoker_uscxml PROPERTIES RUNTIME_OUTPUT_DIRECTORY "${OUTPUT_DIR}/lib")
else()
	list (APPEND USCXML_FILES ${USCXML_INVOKER})
endif()


# HTTP server invoker 

set(USCXML_INVOKERS "httpservlet ${USCXML_INVOKERS}")
file(GLOB_RECURSE HTTPSERVLET_INVOKER 
	http/*.cpp 
	http/*.h)
if (BUILD_AS_PLUGINS)
	source_group("" FILES ${HTTPSERVLET_INVOKER})
	add_library(
		invoker_httpserver SHARED 
		${HTTPSERVLET_INVOKER}
		"../Plugins.cpp")
	target_link_libraries(invoker_httpserver 
		uscxml)
		set_target_properties(invoker_httpserver PROPERTIES FOLDER "Plugin Invoker")
		set_target_properties(invoker_httpserver PROPERTIES COMPILE_FLAGS "-DPLUMA_EXPORTS")
		set_target_properties(invoker_httpserver PROPERTIES RUNTIME_OUTPUT_DIRECTORY "${OUTPUT_DIR}/lib")
else()
	list (APPEND USCXML_FILES ${HTTPSERVLET_INVOKER})
endif()


# Heartbeat invoker

set(USCXML_INVOKERS "heartbeat ${USCXML_INVOKERS}")
file(GLOB_RECURSE HEARTBEAT_INVOKER
	heartbeat/*.cpp
	heartbeat/*.h
)
if (BUILD_AS_PLUGINS)
	source_group("" FILES ${HEARTBEAT_INVOKER})
	add_library(
		invoker_heartbeat SHARED 
		${HEARTBEAT_INVOKER}
		"../Plugins.cpp")
	target_link_libraries(invoker_heartbeat uscxml)
	set_target_properties(invoker_heartbeat PROPERTIES FOLDER "Plugin Invoker")
	set_target_properties(invoker_heartbeat PROPERTIES COMPILE_FLAGS "-DPLUMA_EXPORTS")
	set_target_properties(invoker_heartbeat PROPERTIES RUNTIME_OUTPUT_DIRECTORY "${OUTPUT_DIR}/lib")
else()
	list (APPEND USCXML_FILES ${HEARTBEAT_INVOKER})
endif()


# OpenSceneGraph invoker
if (OPENSCENEGRAPH_FOUND AND OPENGL_FOUND)
	set(USCXML_INVOKERS "scenegraph ${USCXML_INVOKERS}")
	file(GLOB OPENSCENEGRAPH_INVOKER 
		graphics/openscenegraph/*.cpp 
		graphics/openscenegraph/*.h)

	if (BUILD_AS_PLUGINS)
		source_group("" FILES ${OPENSCENEGRAPH_INVOKER})
		add_library(
			invoker_openscenegraph SHARED 
			${OPENSCENEGRAPH_INVOKER}
			"../Plugins.cpp")
		target_link_libraries(invoker_openscenegraph
			${OPENSCENEGRAPH_LIBRARIES}
			${OPENGL_LIBRARIES}
			uscxml)
			set_target_properties(invoker_openscenegraph PROPERTIES FOLDER "Plugin Invoker")
			set_target_properties(invoker_openscenegraph PROPERTIES COMPILE_FLAGS "-DPLUMA_EXPORTS")
			set_target_properties(invoker_openscenegraph PROPERTIES RUNTIME_OUTPUT_DIRECTORY "${OUTPUT_DIR}/lib")
	else()
		list (APPEND USCXML_FILES ${OPENSCENEGRAPH_INVOKER})
	endif()

	set(USCXML_INVOKERS "osgvonvert ${USCXML_INVOKERS}")
	file(GLOB OPENSCENEGRAPH_CONVERTER_INVOKER 
		graphics/openscenegraph/converter/*.cpp 
		graphics/openscenegraph/converter/*.h)

	if (BUILD_AS_PLUGINS)
		source_group("" FILES ${OPENSCENEGRAPH_CONVERTER_INVOKER})
		add_library(
			invoker_openscenegraph_convert SHARED 
			${OPENSCENEGRAPH_CONVERTER_INVOKER}
			"../Plugins.cpp")
		target_link_libraries(invoker_openscenegraph_convert
			${OPENSCENEGRAPH_LIBRARIES}
			${OPENGL_LIBRARIES}
			uscxml)
			set_target_properties(invoker_openscenegraph_convert PROPERTIES FOLDER "Plugin Invoker")
			set_target_properties(invoker_openscenegraph_convert PROPERTIES COMPILE_FLAGS "-DPLUMA_EXPORTS")
			set_target_properties(invoker_openscenegraph_convert PROPERTIES RUNTIME_OUTPUT_DIRECTORY "${OUTPUT_DIR}/lib")
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
#	message("MILES_INVOKER ${MILES_INVOKER}")

	if (BUILD_AS_PLUGINS)
		source_group("" FILES ${OPENAL_INVOKER})
		add_library(
			invoker_openal SHARED 
			${OPENAL_INVOKER}
			"../Plugins.cpp")
		if (LIBSNDFILE_FOUND)
			target_link_libraries(invoker_openal 
				${OPENAL_LIBRARY}
				${LIBSNDFILE_LIBRARY}
				uscxml)
		elseif(AUDIOTOOLBOX_FOUND)
			target_link_libraries(invoker_openal 
				${OPENAL_LIBRARY}
				${AUDIOTOOLBOX}/AudioToolbox
				uscxml)
		endif()	
		set_target_properties(invoker_openal PROPERTIES FOLDER "Plugin Invoker")
		set_target_properties(invoker_openal PROPERTIES COMPILE_FLAGS "-DPLUMA_EXPORTS")
		set_target_properties(invoker_openal PROPERTIES RUNTIME_OUTPUT_DIRECTORY "${OUTPUT_DIR}/lib")
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
#	message("MILES_INVOKER ${MILES_INVOKER}")

	if (BUILD_AS_PLUGINS)
		source_group("" FILES ${MILES_INVOKER})
		add_library(
			invoker_miles SHARED 
			${MILES_INVOKER}
			"../Plugins.cpp")
		target_link_libraries(invoker_miles 
			${MILES_LIBRARIES}
			${JPEG_LIBRARIES}
			uscxml)
			if (ICONV_FOUND)
				target_link_libraries(invoker_miles ${ICONV_LIBRARIES})
			endif()
			if (OPENAL_FOUND)
				target_link_libraries(invoker_miles ${OPENAL_LIBRARY})
			endif()
		set_target_properties(invoker_miles PROPERTIES FOLDER "Plugin Invoker")
		set_target_properties(invoker_miles PROPERTIES COMPILE_FLAGS "-DPLUMA_EXPORTS")
		set_target_properties(invoker_miles PROPERTIES RUNTIME_OUTPUT_DIRECTORY "${OUTPUT_DIR}/lib")
	else()
  	list (APPEND USCXML_FILES ${MILES_INVOKER})
	endif()
endif()


# VoiceXML modality components

if (UMUNDO_FOUND AND OFF)
	set(USCXML_INVOKERS "vxml ${USCXML_INVOKERS}")
	file(GLOB_RECURSE VXML_INVOKER
		vxml/*.cpp
		vxml/*.h
	)
	if (BUILD_AS_PLUGINS)
		source_group("" FILES ${VXML_INVOKER})
		add_library(
			invoker_voicexml SHARED 
			${VXML_INVOKER}
			"../Plugins.cpp")
		target_link_libraries(invoker_voicexml uscxml)
		set_target_properties(invoker_voicexml PROPERTIES FOLDER "Plugin Invoker")
		set_target_properties(invoker_voicexml PROPERTIES COMPILE_FLAGS "-DPLUMA_EXPORTS")
		set_target_properties(invoker_voicexml PROPERTIES RUNTIME_OUTPUT_DIRECTORY "${OUTPUT_DIR}/lib")
	else()
		list (APPEND USCXML_FILES ${VXML_INVOKER})
	endif()
endif()

set(USCXML_INCLUDE_DIRS ${USCXML_INCLUDE_DIRS} PARENT_SCOPE)
set(USCXML_FILES ${USCXML_FILES} PARENT_SCOPE)
set(USCXML_INVOKERS ${USCXML_INVOKERS} PARENT_SCOPE)
