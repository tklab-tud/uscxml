# Respond element 

OPTION(WITH_ELEMENT_RESPOND "Build the respond element" ON)
if (WITH_ELEMENT_RESPOND)
	set(USCXML_ELEMENTS "respond ${USCXML_ELEMENTS}")
	file(GLOB_RECURSE ELEMENT_RESPOND 
		respond/*.cpp 
		respond/*.h)
	if (BUILD_AS_PLUGINS)
		source_group("" FILES ${ELEMENT_RESPOND})
		add_library(element_respond SHARED ${ELEMENT_RESPOND} "../Plugins.cpp")
		target_link_libraries(element_respond 
			uscxml
		)
		set_target_properties(element_respond PROPERTIES FOLDER "Plugins//Elements")
		set_target_properties(element_respond PROPERTIES COMPILE_FLAGS "-DPLUMA_EXPORTS")
		set_target_properties(element_respond PROPERTIES LIBRARY_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/lib/plugins")
	else()
		list (APPEND USCXML_FILES ${ELEMENT_RESPOND})
	endif()			
endif()
	
	
set(USCXML_INCLUDE_DIRS ${USCXML_INCLUDE_DIRS} PARENT_SCOPE)
set(USCXML_FILES ${USCXML_FILES} PARENT_SCOPE)
set(USCXML_ELEMENTS ${USCXML_ELEMENTS} PARENT_SCOPE)
