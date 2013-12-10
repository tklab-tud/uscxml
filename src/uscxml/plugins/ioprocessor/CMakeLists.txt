#set(USCXML_IOPROCESSORS "sample ${USCXML_IOPROCESSORS}")
#file(GLOB_RECURSE SAMPLE_IOPROCESSOR
#	sample/*.cpp
#	sample/*.h
#)
#if (BUILD_AS_PLUGINS)
#	source_group("" FILES ${SAMPLE_IOPROCESSOR})
#	add_library(
#		ioprocessor_sample SHARED
#		${SAMPLE_IOPROCESSOR}
#		"../Plugins.cpp")
#	target_link_libraries(ioprocessor_sample uscxml)
#	set_target_properties(ioprocessor_sample PROPERTIES FOLDER "Plugin IOProcessor")
#else()
#	list (APPEND USCXML_FILES ${SAMPLE_IOPROCESSOR})
#endif()

#set(USCXML_IOPROCESSORS "comet ${USCXML_IOPROCESSORS}")
#file(GLOB_RECURSE COMET_IOPROCESSOR
#	comet/*.cpp
#	comet/*.h
#)
#if (BUILD_AS_PLUGINS)
#	source_group("" FILES ${COMET_IOPROCESSOR})
#	add_library(
#		ioprocessor_comet SHARED
#		${COMET_IOPROCESSOR}
#		"../Plugins.cpp")
#	target_link_libraries(ioprocessor_comet uscxml)
#	set_target_properties(ioprocessor_comet PROPERTIES FOLDER "Plugin IOProcessor")
#else()
#	list (APPEND USCXML_FILES ${COMET_IOPROCESSOR})
#endif()


# LIBEVENT basichttp ioprocessor - this one is already required above

set(USCXML_IOPROCESSORS "basichttp ${USCXML_IOPROCESSORS}")
file(GLOB_RECURSE BASICHTTP_IOPROCESSOR
	basichttp/*.cpp
	basichttp/*.h
)
if (BUILD_AS_PLUGINS)
	source_group("" FILES ${BASICHTTP_IOPROCESSOR})
	add_library(
		ioprocessor_basichttp SHARED 
		${BASICHTTP_IOPROCESSOR}
		"../Plugins.cpp")
	target_link_libraries(ioprocessor_basichttp uscxml)
	set_target_properties(ioprocessor_basichttp PROPERTIES FOLDER "Plugin IOProcessor")
else()
	list (APPEND USCXML_FILES ${BASICHTTP_IOPROCESSOR})
endif()


# scxml ioprocessor - this one is already required above

set(USCXML_IOPROCESSORS "scxml ${USCXML_IOPROCESSORS}")
file(GLOB_RECURSE SCXML_IOPROCESSOR
	scxml/*.cpp
	scxml/*.h
)
if (BUILD_AS_PLUGINS)
	source_group("" FILES ${SCXML_IOPROCESSOR})
	add_library(
		ioprocessor_scxml SHARED 
		${SCXML_IOPROCESSOR}
		"../Plugins.cpp")
	# scxml ioprocessor is a basichttp ioprocessor
	target_link_libraries(ioprocessor_scxml ioprocessor_basichttp uscxml)
	set_target_properties(ioprocessor_scxml PROPERTIES FOLDER "Plugin IOProcessor")
else()
	list (APPEND USCXML_FILES ${SCXML_IOPROCESSOR})
endif()


# mmi ioprocessor

if (PROTOBUF_FOUND AND OFF)

	if (NOT PROTOBUF_PROTOC_EXECUTABLE)
		message(FATAL_ERROR "protoc binary required for serialization")
	endif()

	set(USCXML_IOPROCESSORS "mmi ${USCXML_IOPROCESSORS}")
	file(GLOB_RECURSE MMI_IOPROCESSOR
		modality/*.cpp
		modality/*.h
	)

	# process .proto files
	file(GLOB_RECURSE PROTOBUF_INTERFACES ${PROJECT_SOURCE_DIR}/contrib/proto/*.proto)
	list (APPEND USCXML_INCLUDE_DIRS ${CMAKE_CURRENT_BINARY_DIR})

	PROTOBUF_GENERATE_CPP(PROTO_SRCS PROTO_HDRS ${PROTOBUF_INTERFACES})
#	set_source_files_properties(${PROTO_SRCS} ${PROTO_HDRS} PROPERTIES GENERATED TRUE)

	# this needs to be here for dependencies on the generated proto files
	add_library(mmi_proto STATIC ${PROTO_SRCS})
	set_target_properties(mmi_proto PROPERTIES FOLDER "Generated")

	if (BUILD_AS_PLUGINS)
		source_group("" FILES ${MMI_IOPROCESSOR})
		add_library(
			ioprocessor_mmi SHARED 
			${MMI_IOPROCESSOR}
			"../Plugins.cpp")
		target_link_libraries(ioprocessor_mmi uscxml mmi_proto)
		set_target_properties(ioprocessor_mmi PROPERTIES FOLDER "Plugin IOProcessor")
	else()
		list (APPEND USCXML_FILES ${MMI_IOPROCESSOR})
		list (APPEND USCXML_OPT_LIBS mmi_proto)
	endif()
endif()

set(USCXML_INCLUDE_DIRS ${USCXML_INCLUDE_DIRS} PARENT_SCOPE)
set(USCXML_OPT_LIBS ${USCXML_OPT_LIBS} PARENT_SCOPE)
set(USCXML_FILES ${USCXML_FILES} PARENT_SCOPE)
set(USCXML_IOPROCESSORS ${USCXML_IOPROCESSORS} PARENT_SCOPE)
