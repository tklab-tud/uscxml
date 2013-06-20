file(GLOB_RECURSE SAMPLE_IOPROCESSOR
	sample/*.cpp
	sample/*.h
)
source_group("IOProcessor\\sample" FILES ${SAMPLE_IOPROCESSOR})
if (BUILD_AS_PLUGINS)
	add_library(
		ioprocessor_sample SHARED 
		${SAMPLE_IOPROCESSOR})
	target_link_libraries(ioprocessor_sample uscxml)
	set_target_properties(ioprocessor_sample PROPERTIES FOLDER "Plugin IOProcessor")
else()
	list (APPEND USCXML_FILES ${SAMPLE_IOPROCESSOR})
endif()

file(GLOB_RECURSE COMET_IOPROCESSOR
	comet/*.cpp
	comet/*.h
)
source_group("IOProcessor\\comet" FILES ${COMET_IOPROCESSOR})
if (BUILD_AS_PLUGINS)
	add_library(
		ioprocessor_comet SHARED 
		${COMET_IOPROCESSOR})
	target_link_libraries(ioprocessor_comet uscxml)
	set_target_properties(ioprocessor_comet PROPERTIES FOLDER "Plugin IOProcessor")
else()
	list (APPEND USCXML_FILES ${COMET_IOPROCESSOR})
endif()


# LIBEVENT basichttp ioprocessor - this one is already required above

file(GLOB_RECURSE BASICHTTP_IOPROCESSOR
	basichttp/*.cpp
	basichttp/*.h
)
source_group("IOProcessor\\basichttp" FILES ${BASICHTTP_IOPROCESSOR})
if (BUILD_AS_PLUGINS)
	add_library(
		ioprocessor_basichttp SHARED 
		${BASICHTTP_IOPROCESSOR})
	target_link_libraries(ioprocessor_basichttp uscxml)
	set_target_properties(ioprocessor_basichttp PROPERTIES FOLDER "Plugin IOProcessor")
else()
	list (APPEND USCXML_FILES ${BASICHTTP_IOPROCESSOR})
endif()


# scxml ioprocessor - this one is already required above

file(GLOB_RECURSE SCXML_IOPROCESSOR
	scxml/*.cpp
	scxml/*.h
)
source_group("IOProcessor\\scxml" FILES ${SCXML_IOPROCESSOR})
if (BUILD_AS_PLUGINS)
	add_library(
		ioprocessor_scxml SHARED 
		${SCXML_IOPROCESSOR})
	target_link_libraries(ioprocessor_scxml uscxml)
	set_target_properties(ioprocessor_scxml PROPERTIES FOLDER "Plugin IOProcessor")
else()
	list (APPEND USCXML_FILES ${SCXML_IOPROCESSOR})
endif()


# mmi ioprocessor

if (PROTOBUF_FOUND)

	if (NOT PROTOBUF_PROTOC_EXECUTABLE)
		message(FATAL_ERROR "protoc binary required for serialization")
	endif()

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

	source_group("IOProcessor\\modality" FILES ${MMI_IOPROCESSOR})
	if (BUILD_AS_PLUGINS)
		add_library(
			ioprocessor_mmi SHARED 
			${MMI_IOPROCESSOR})
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
