if (JSC_FOUND AND BUILD_DM_ECMA)
	# JavaScriptCore ecmascript datamodel
	file(GLOB JSC_DATAMODEL
		ecmascript/JavaScriptCore/*.cpp
		ecmascript/JavaScriptCore/*.h
	)
	source_group("Datamodel\\jsc" FILES ${JSC_DATAMODEL})
	file(GLOB_RECURSE JSC_DOM
		ecmascript/JavaScriptCore/dom/*.cpp
		ecmascript/JavaScriptCore/dom/*.h
	)
	source_group("Datamodel\\DOM" FILES ${JSC_DOM})
	if (BUILD_AS_PLUGINS)
		add_library(
			datamodel_jsc SHARED 
			${JSC_DATAMODEL}
			${JSC_DOM})
		target_link_libraries(datamodel_jsc 
			uscxml
			${JSC_LIBRARY})
		set_target_properties(datamodel_jsc PROPERTIES FOLDER "Plugin DataModel")
	else()
		list (APPEND USCXML_FILES ${JSC_DATAMODEL})
		list (APPEND USCXML_FILES ${JSC_DOM})
		list (APPEND USCXML_OPT_LIBS ${JSC_LIBRARY})
	endif()
else()

# GOOGLE V8 ecmascript datamodel
	# set(ENV{V8_SRC} ${CMAKE_SOURCE_DIR}/../v8)
	if (V8_FOUND AND BUILD_DM_ECMA)
		file(GLOB V8_DATAMODEL
			ecmascript/v8/*.cpp
			ecmascript/v8/*.h
		)
		source_group("Datamodel\\v8" FILES ${V8_DATAMODEL})
		file(GLOB_RECURSE V8_DOM
			ecmascript/v8/dom/*.cpp
			ecmascript/v8/dom/*.h
		)
		source_group("Datamodel\\v8\\DOM" FILES ${V8_DOM})

		if (BUILD_AS_PLUGINS)
			add_library(
				datamodel_v8 SHARED 
				${V8_DATAMODEL}
				${V8_DOM})
			target_link_libraries(datamodel_v8 
				uscxml
				${V8_LIBRARY})
			set_target_properties(datamodel_v8 PROPERTIES FOLDER "Plugin DataModel")
		else()
			list (APPEND USCXML_FILES ${V8_DATAMODEL})
			list (APPEND USCXML_FILES ${V8_DOM})
		endif()
	endif()
endif()


# NULL datamodel

file(GLOB NULL_DATAMODEL
	null/*.cpp
	null/*.h
)
source_group("Datamodel\\null" FILES ${NULL_DATAMODEL})
if (BUILD_AS_PLUGINS)
	add_library(datamodel_null SHARED ${NULL_DATAMODEL})
	target_link_libraries(datamodel_null uscxml)
	set_target_properties(datamodel_null PROPERTIES FOLDER "Plugin DataModel")
else()
	list (APPEND USCXML_FILES ${NULL_DATAMODEL})
endif()


# XPath datamodel

if (BUILD_DM_XPATH)
	file(GLOB XPATH_DATAMODEL
		xpath/*.cpp
		xpath/*.h
	)
	source_group("Datamodel\\xpath" FILES ${XPATH_DATAMODEL})
	if (BUILD_AS_PLUGINS)
		add_library(datamodel_xpath SHARED ${XPATH_DATAMODEL})
		target_link_libraries(datamodel_xpath uscxml)
		set_target_properties(datamodel_xpath PROPERTIES FOLDER "Plugin DataModel")
	else()
		list (APPEND USCXML_FILES ${XPATH_DATAMODEL})
	endif()
endif()

# SWI PROLOG datamodel

if (SWI_FOUND AND BUILD_DM_PROLOG)
#	message(FATAL_ERROR "SWI_INCLUDE_DIR: ${SWI_INCLUDE_DIR}")

	# if(${CMAKE_CXX_COMPILER_ID} STREQUAL "Clang")
	# 	set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -read_only_relocs suppress")
	# 	set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -read_only_relocs suppress")
	# 	set(CMAKE_MODULE_LINKER_FLAGS "${CMAKE_MODULE_LINKER_FLAGS} -read_only_relocs suppress")
	# 	set(CMAKE_LINKER_FLAGS "${CMAKE_LINKER_FLAGS} -read_only_relocs suppress")
	# endif()
	file(GLOB_RECURSE SWI_DATAMODEL
		prolog/swi/*.cpp
		prolog/swi/*.h
	)
	source_group("Datamodel\\swi" FILES ${SWI_DATAMODEL})
	if (BUILD_AS_PLUGINS)
		add_library(
			datamodel_swi SHARED 
			${SWI_DATAMODEL})
		target_link_libraries(datamodel_swi 
			uscxml
			${GMP_LIBRARY}
			${CURSES_LIBRARIES}
			${SWI_LIBRARY})
		set_target_properties(datamodel_swi PROPERTIES FOLDER "Plugin DataModel")
	else()
		list (APPEND USCXML_FILES ${SWI_DATAMODEL})
	endif()
endif()

set(USCXML_INCLUDE_DIRS ${USCXML_INCLUDE_DIRS} PARENT_SCOPE)
set(USCXML_FILES ${USCXML_FILES} PARENT_SCOPE)