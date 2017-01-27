# scxml ioprocessor

OPTION(WITH_IOPROC_SCXML "Build the scxml i/o processor" ON)
if (WITH_IOPROC_SCXML)
	set(USCXML_IOPROCESSORS "scxml ${USCXML_IOPROCESSORS}")
	file(GLOB_RECURSE SCXML_IOPROCESSOR
		scxml/*.cpp
		scxml/*.h
	)
	if (BUILD_AS_PLUGINS)
		source_group("" FILES ${SCXML_IOPROCESSOR})
		add_library(ioproc_scxml SHARED ${SCXML_IOPROCESSOR} "../Plugins.cpp")
		target_link_libraries(ioproc_scxml 
			uscxml
		)
		set_target_properties(ioproc_scxml PROPERTIES FOLDER "Plugins//IO Processors")
		set_target_properties(ioproc_scxml PROPERTIES COMPILE_FLAGS "-DPLUMA_EXPORTS")
		set_target_properties(ioproc_scxml PROPERTIES LIBRARY_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/lib/plugins")
	else()
		list (APPEND USCXML_FILES ${SCXML_IOPROCESSOR})
	endif()
endif()

OPTION(WITH_IOPROC_BASICHTTP "Build the basichttp i/o processor" ON)
if (WITH_IOPROC_BASICHTTP)
	set(USCXML_IOPROCESSORS "basichttp ${USCXML_IOPROCESSORS}")
	file(GLOB_RECURSE BASICHTTP_IOPROCESSOR
		basichttp/*.cpp
		basichttp/*.h
	)
	if (BUILD_AS_PLUGINS)
		source_group("" FILES ${BASICHTTP_IOPROCESSOR})
		add_library(ioproc_basichttp SHARED ${BASICHTTP_IOPROCESSOR} "../Plugins.cpp")
		target_link_libraries(ioproc_basichttp 
			uscxml
		)
		set_target_properties(ioproc_basichttp PROPERTIES FOLDER "Plugins//IO Processors")
		set_target_properties(ioproc_basichttp PROPERTIES COMPILE_FLAGS "-DPLUMA_EXPORTS")
		set_target_properties(ioproc_basichttp PROPERTIES LIBRARY_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/lib/plugins")
	else()
		list (APPEND USCXML_FILES ${BASICHTTP_IOPROCESSOR})
	endif()
endif()

set(USCXML_INCLUDE_DIRS ${USCXML_INCLUDE_DIRS} PARENT_SCOPE)
set(USCXML_OPT_LIBS ${USCXML_OPT_LIBS} PARENT_SCOPE)
set(USCXML_FILES ${USCXML_FILES} PARENT_SCOPE)
set(USCXML_IOPROCESSORS ${USCXML_IOPROCESSORS} PARENT_SCOPE)
