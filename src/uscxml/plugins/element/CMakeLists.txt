# Fetch element

set(USCXML_ELEMENTS "fetch ${USCXML_ELEMENTS}")
file(GLOB_RECURSE FETCH_ELEMENT
	fetch/*.cpp
	fetch/*.h
)
if (BUILD_AS_PLUGINS)
	source_group("" FILES ${FETCH_ELEMENT})
	add_library(
		element_fetch SHARED 
		${FETCH_ELEMENT}
		"../Plugins.cpp")
	target_link_libraries(element_fetch uscxml)
	set_target_properties(element_fetch PROPERTIES FOLDER "Plugin Element")
	set_target_properties(element_fetch PROPERTIES COMPILE_FLAGS "-DPLUMA_EXPORTS")
	set_target_properties(element_fetch PROPERTIES RUNTIME_OUTPUT_DIRECTORY "${OUTPUT_DIR}/lib")
else()
	list (APPEND USCXML_FILES ${FETCH_ELEMENT})
endif()

# MMI elements

# file(GLOB_RECURSE MMI_ELEMENT
# 	mmi/*.cpp
# 	mmi/*.h
# )
# if (BUILD_AS_PLUGINS)
# 	source_group("" FILES ${MMI_ELEMENT})
# 	add_library(
# 		element_mmi SHARED 
# 		${MMI_ELEMENT}
# 		"../Plugins.cpp")
# 	target_link_libraries(element_mmi uscxml)
# 	set_target_properties(element_mmi PROPERTIES FOLDER "Plugin Element")
# 	set_target_properties(element_mmi PROPERTIES COMPILE_FLAGS "-DPLUMA_EXPORTS")
# 	set_target_properties(element_mmi PROPERTIES RUNTIME_OUTPUT_DIRECTORY "${OUTPUT_DIR}/lib")
# else()
# 	list (APPEND USCXML_FILES ${MMI_ELEMENT})
# endif()


# Postpone element

set(USCXML_ELEMENTS "postpone ${USCXML_ELEMENTS}")
file(GLOB_RECURSE POSTPONE_ELEMENT
	postpone/*.cpp
	postpone/*.h
)
if (BUILD_AS_PLUGINS)
	source_group("" FILES ${POSTPONE_ELEMENT})
	add_library(
		element_postpone SHARED 
		${POSTPONE_ELEMENT}
		"../Plugins.cpp")
	target_link_libraries(element_postpone uscxml)
	set_target_properties(element_postpone PROPERTIES FOLDER "Plugin Element")
	set_target_properties(element_postpone PROPERTIES COMPILE_FLAGS "-DPLUMA_EXPORTS")
	set_target_properties(element_postpone PROPERTIES RUNTIME_OUTPUT_DIRECTORY "${OUTPUT_DIR}/lib")
else()
	list (APPEND USCXML_FILES ${POSTPONE_ELEMENT})
endif()


# File element

set(USCXML_ELEMENTS "file ${USCXML_ELEMENTS}")
file(GLOB_RECURSE FILE_ELEMENT
	file/*.cpp
	file/*.h
)
if (BUILD_AS_PLUGINS)
	source_group("" FILES ${FILE_ELEMENT})
	add_library(
		element_file SHARED 
		${FILE_ELEMENT}
		"../Plugins.cpp")
	target_link_libraries(element_file uscxml)
	set_target_properties(element_file PROPERTIES FOLDER "Plugin Element")
	set_target_properties(element_file PROPERTIES COMPILE_FLAGS "-DPLUMA_EXPORTS")
	set_target_properties(element_file PROPERTIES RUNTIME_OUTPUT_DIRECTORY "${OUTPUT_DIR}/lib")
else()
	list (APPEND USCXML_FILES ${FILE_ELEMENT})
endif()


# Respond element

set(USCXML_ELEMENTS "respond ${USCXML_ELEMENTS}")
file(GLOB_RECURSE RESPOND_ELEMENT
	respond/*.cpp
	respond/*.h
)
if (BUILD_AS_PLUGINS)
	source_group("" FILES ${RESPOND_ELEMENT})
	add_library(
		element_respond SHARED 
		${RESPOND_ELEMENT}
		"../Plugins.cpp")
	target_link_libraries(element_respond uscxml)
	set_target_properties(element_respond PROPERTIES FOLDER "Plugin Element")
	set_target_properties(element_respond PROPERTIES COMPILE_FLAGS "-DPLUMA_EXPORTS")
	set_target_properties(element_respond PROPERTIES RUNTIME_OUTPUT_DIRECTORY "${OUTPUT_DIR}/lib")
else()
	list (APPEND USCXML_FILES ${RESPOND_ELEMENT})
endif()

set(USCXML_INCLUDE_DIRS ${USCXML_INCLUDE_DIRS} PARENT_SCOPE)
set(USCXML_FILES ${USCXML_FILES} PARENT_SCOPE)
set(USCXML_ELEMENTS ${USCXML_ELEMENTS} PARENT_SCOPE)
