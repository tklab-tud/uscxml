# Fetch element

file(GLOB_RECURSE FETCH_ELEMENT
	fetch/*.cpp
	fetch/*.h
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

# MMI elements

# file(GLOB_RECURSE MMI_ELEMENT
# 	mmi/*.cpp
# 	mmi/*.h
# )
# source_group("Element\\mmi" FILES ${MMI_ELEMENT})
# if (BUILD_AS_PLUGINS)
# 	add_library(
# 		element_mmi SHARED 
# 		${MMI_ELEMENT})
# 	target_link_libraries(element_mmi uscxml)
# 	set_target_properties(element_mmi PROPERTIES FOLDER "Plugin Element")
# else()
# 	list (APPEND USCXML_FILES ${MMI_ELEMENT})
# endif()


# Postpone element

file(GLOB_RECURSE POSTPONE_ELEMENT
	postpone/*.cpp
	postpone/*.h
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
	respond/*.cpp
	respond/*.h
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

set(USCXML_INCLUDE_DIRS ${USCXML_INCLUDE_DIRS} PARENT_SCOPE)
set(USCXML_FILES ${USCXML_FILES} PARENT_SCOPE)