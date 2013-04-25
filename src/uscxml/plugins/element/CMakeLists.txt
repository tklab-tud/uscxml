# Fetch element

file(GLOB_RECURSE FETCH_ELEMENT
	src/uscxml/plugins/element/fetch/*.cpp
	src/uscxml/plugins/element/fetch/*.h
)
source_group("Element\\fetch" FILES ${FETCH_ELEMENT})
if (BUILD_AS_PLUGINS)
	add_library(
		element_fetch SHARED 
		${FETCH_ELEMENT})
	target_link_libraries(element_fetch uscxml)
	set_target_properties(element_fetch PROPERTIES FOLDER "Plugin Element")
else()
	list (APPEND USCXML_FILES ${FETCH_ELEMENT})
endif()


# Postpone element

file(GLOB_RECURSE POSTPONE_ELEMENT
	src/uscxml/plugins/element/postpone/*.cpp
	src/uscxml/plugins/element/postpone/*.h
)
source_group("Element\\postpone" FILES ${POSTPONE_ELEMENT})
if (BUILD_AS_PLUGINS)
	add_library(
		element_postpone SHARED 
		${POSTPONE_ELEMENT})
	target_link_libraries(element_postpone uscxml)
	set_target_properties(element_postpone PROPERTIES FOLDER "Plugin Element")
else()
	list (APPEND USCXML_FILES ${POSTPONE_ELEMENT})
endif()


# Respond element

file(GLOB_RECURSE RESPOND_ELEMENT
	src/uscxml/plugins/element/respond/*.cpp
	src/uscxml/plugins/element/respond/*.h
)
source_group("Element\\respond" FILES ${RESPOND_ELEMENT})
if (BUILD_AS_PLUGINS)
	add_library(
		element_respond SHARED 
		${RESPOND_ELEMENT})
	target_link_libraries(element_respond uscxml)
	set_target_properties(element_respond PROPERTIES FOLDER "Plugin Element")
else()
	list (APPEND USCXML_FILES ${RESPOND_ELEMENT})
endif()

