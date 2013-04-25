# JavaScriptCore ecmascript datamodel
if (APPLE AND IOS AND OFF)
	FIND_LIBRARY(JSC_LIBRARY JavaScriptCore)
	set(JSC_FOUND ON)
	file(GLOB JSC_DATAMODEL
		src/uscxml/plugins/datamodel/ecmascript/JavaScriptCore/*.cpp
		src/uscxml/plugins/datamodel/ecmascript/JavaScriptCore/*.h
	)
	source_group("Datamodel\\jsc" FILES ${JSC_DATAMODEL})
	file(GLOB_RECURSE JSC_DOM
		src/uscxml/plugins/datamodel/ecmascript/JavaScriptCore/dom/*.cpp
		src/uscxml/plugins/datamodel/ecmascript/JavaScriptCore/dom/*.h
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

endif()


# NULL datamodel

file(GLOB NULL_DATAMODEL
	src/uscxml/plugins/datamodel/null/*.cpp
	src/uscxml/plugins/datamodel/null/*.h
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

file(GLOB XPATH_DATAMODEL
	src/uscxml/plugins/datamodel/xpath/*.cpp
	src/uscxml/plugins/datamodel/xpath/*.h
)
source_group("Datamodel\\xpath" FILES ${XPATH_DATAMODEL})
if (BUILD_AS_PLUGINS)
	add_library(datamodel_xpath SHARED ${XPATH_DATAMODEL})
	target_link_libraries(datamodel_xpath uscxml)
	set_target_properties(datamodel_xpath PROPERTIES FOLDER "Plugin DataModel")
else()
	list (APPEND USCXML_FILES ${XPATH_DATAMODEL})
endif()


# GOOGLE V8 ecmascript datamodel

#if (NOT APPLE OR IOS)
	# set(ENV{V8_SRC} ${CMAKE_SOURCE_DIR}/../v8)
	find_package(V8)
	if (V8_FOUND)
		list (APPEND USCXML_INCLUDE_DIRS ${V8_INCLUDE_DIR})
		file(GLOB V8_DATAMODEL
			src/uscxml/plugins/datamodel/ecmascript/v8/*.cpp
			src/uscxml/plugins/datamodel/ecmascript/v8/*.h
		)
		source_group("Datamodel\\v8" FILES ${V8_DATAMODEL})
		file(GLOB_RECURSE V8_DOM
			src/uscxml/plugins/datamodel/ecmascript/v8/dom/*.cpp
			src/uscxml/plugins/datamodel/ecmascript/v8/dom/*.h
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
			list (APPEND USCXML_OPT_LIBS ${V8_LIBRARY})
		endif()
	endif()
#endif()


# SWI PROLOG datamodel

#set(SWI_INCLUDE_HINT ${CMAKE_SOURCE_DIR}/../pl-devel/include)
#set(SWI_LIBRARY_HINT ${CMAKE_SOURCE_DIR}/../pl-devel/lib/x86_64-darwin12.2.0)
find_package(SWI)
#find_package(GMP)
#find_package(CURSES)
if (SWI_FOUND)
	list (APPEND USCXML_INCLUDE_DIRS ${SWI_INCLUDE_DIR})	
#	message(FATAL_ERROR "SWI_INCLUDE_DIR: ${SWI_INCLUDE_DIR}")
#	include_directories(${GMP_INCLUDE_DIR})
#	include_directories(${CURSES_INCLUDE_DIR})
	file(GLOB_RECURSE SWI_DATAMODEL
		src/uscxml/plugins/datamodel/prolog/swi/*.cpp
		src/uscxml/plugins/datamodel/prolog/swi/*.h
	)
	source_group("Datamodel\\swi" FILES ${SWI_DATAMODEL})
	if (BUILD_AS_PLUGINS)
		add_library(
			datamodel_swi SHARED 
			${SWI_DATAMODEL})
		target_link_libraries(datamodel_swi 
			uscxml
#			${GMP_LIBRARY}
#			${CURSES_LIBRARIES}
			${SWI_LIBRARY})
		set_target_properties(datamodel_swi PROPERTIES FOLDER "Plugin DataModel")
	else()
		list (APPEND USCXML_FILES ${SWI_DATAMODEL})
		list (APPEND USCXML_OPT_LIBS ${SWI_LIBRARY}) # ${GMP_LIBRARY} ${CURSES_LIBRARIES})
	endif()
endif()
