# USCXML invoker 

OPTION(WITH_INV_SCXML "Build the SCXML invoker" ON)
if (WITH_INV_SCXML)
	set(USCXML_INVOKERS "scxml ${USCXML_INVOKERS}")
	file(GLOB_RECURSE USCXML_INVOKER 
		scxml/*.cpp 
		scxml/*.h)
	if (BUILD_AS_PLUGINS)
		source_group("" FILES ${USCXML_INVOKER})
		add_library(invoker_uscxml SHARED ${USCXML_INVOKER} "../Plugins.cpp")
		target_link_libraries(invoker_uscxml 
			uscxml
		)
		set_target_properties(invoker_uscxml PROPERTIES FOLDER "Plugins//Invoker")
		set_target_properties(invoker_uscxml PROPERTIES COMPILE_FLAGS "-DPLUMA_EXPORTS")
		set_target_properties(invoker_uscxml PROPERTIES LIBRARY_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/lib/plugins")
	else()
		list (APPEND USCXML_FILES ${USCXML_INVOKER})
	endif()			
endif()
	
# Directoy Monitor 

OPTION(WITH_INV_DIRMON "Build the directory monitor invoker" ON)
if (WITH_INV_DIRMON)
	set(USCXML_INVOKERS "dirmon ${USCXML_INVOKERS}")
	file(GLOB_RECURSE DIRMON_INVOKER 
		dirmon/*.cpp 
		dirmon/*.h)
	if (BUILD_AS_PLUGINS)
		source_group("" FILES ${DIRMON_INVOKER})
		add_library(invoker_dirmon SHARED ${DIRMON_INVOKER} "../Plugins.cpp")
		target_link_libraries(invoker_dirmon 
			uscxml
		)
		set_target_properties(invoker_dirmon PROPERTIES FOLDER "Plugins//Invoker")
		set_target_properties(invoker_dirmon PROPERTIES COMPILE_FLAGS "-DPLUMA_EXPORTS")
		set_target_properties(invoker_dirmon PROPERTIES LIBRARY_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/lib/plugins")
	else()
		list (APPEND USCXML_FILES ${DIRMON_INVOKER})
	endif()
endif()
	
set(USCXML_INCLUDE_DIRS ${USCXML_INCLUDE_DIRS} PARENT_SCOPE)
set(USCXML_FILES ${USCXML_FILES} PARENT_SCOPE)
set(USCXML_INVOKERS ${USCXML_INVOKERS} PARENT_SCOPE)
