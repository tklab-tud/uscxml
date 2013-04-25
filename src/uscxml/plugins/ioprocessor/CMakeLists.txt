# LIBEVENT basichttp ioprocessor - this one is already required above

file(GLOB_RECURSE BASICHTTP_IOPROCESSOR
	src/uscxml/plugins/ioprocessor/basichttp/*.cpp
	src/uscxml/plugins/ioprocessor/basichttp/*.h
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
	src/uscxml/plugins/ioprocessor/scxml/*.cpp
	src/uscxml/plugins/ioprocessor/scxml/*.h
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

file(GLOB_RECURSE MMI_IOPROCESSOR
	src/uscxml/plugins/ioprocessor/modality/*.cpp
	src/uscxml/plugins/ioprocessor/modality/*.h
)
source_group("IOProcessor\\modality" FILES ${MMI_IOPROCESSOR})
if (BUILD_AS_PLUGINS)
	add_library(
		ioprocessor_mmi SHARED 
		${MMI_IOPROCESSOR})
	target_link_libraries(ioprocessor_mmi uscxml)
	set_target_properties(ioprocessor_mmi PROPERTIES FOLDER "Plugin IOProcessor")
else()
	list (APPEND USCXML_FILES ${MMI_IOPROCESSOR})
endif()

