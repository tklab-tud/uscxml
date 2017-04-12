# NULL datamodel (not useful as plugin)

set(USCXML_DATAMODELS "null ${USCXML_DATAMODELS}")
file(GLOB NULL_DATAMODEL
	null/*.cpp
	null/*.h
)
if (BUILD_AS_PLUGINS)
	source_group("Null" FILES ${NULL_DATAMODEL})
	add_library(
		datamodel_null SHARED 
		${NULL_DATAMODEL}
	"../Plugins.cpp")
	target_link_libraries(datamodel_null uscxml)
	set_target_properties(datamodel_null PROPERTIES FOLDER "Plugins//DataModel")
	set_target_properties(datamodel_null PROPERTIES COMPILE_FLAGS "-DPLUMA_EXPORTS")
	set_target_properties(datamodel_null PROPERTIES LIBRARY_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/lib/plugins")
else()		
	list (APPEND USCXML_FILES ${NULL_DATAMODEL})
endif()

if (JSC_FOUND)
	set(USCXML_DATAMODELS "ecmascript(JSC) ${USCXML_DATAMODELS}")
	# JavaScriptCore ecmascript datamodel
	file(GLOB JSC_DATAMODEL
		ecmascript/JavaScriptCore/*.cpp
		ecmascript/JavaScriptCore/*.h
		ecmascript/*.cpp
		ecmascript/*.h
	)
	if (BUILD_AS_PLUGINS)
		source_group("JavaScriptCore" FILES ${JSC_DATAMODEL})
		add_library(
			datamodel_jsc SHARED 
			${JSC_DATAMODEL}
		"../Plugins.cpp")
		target_link_libraries(datamodel_jsc uscxml ${JSC_LIBRARY})
		set_target_properties(datamodel_jsc PROPERTIES FOLDER "Plugins//DataModel")
		set_target_properties(datamodel_jsc PROPERTIES COMPILE_FLAGS "-DPLUMA_EXPORTS")
		set_target_properties(datamodel_jsc PROPERTIES LIBRARY_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/lib/plugins")
	else()		
		list (APPEND USCXML_FILES ${JSC_DATAMODEL})
		list (APPEND USCXML_OPT_LIBS ${JSC_LIBRARY})
	endif()
endif()


if (V8_FOUND)
	set(USCXML_DATAMODELS "ecmascript(V8) ${USCXML_DATAMODELS}")
	# JavaScriptCore ecmascript datamodel
	file(GLOB V8_DATAMODEL
		ecmascript/v8/*.cpp
		ecmascript/v8/*.h
		ecmascript/*.cpp
		ecmascript/*.h
	)
	if (BUILD_AS_PLUGINS)
		source_group("V8" FILES ${V8_DATAMODEL})

		add_library(
			datamodel_v8 SHARED 
			${V8_DATAMODEL}
		"../Plugins.cpp")
		target_link_libraries(datamodel_v8 uscxml ${V8_LIBRARY})
		set_target_properties(datamodel_v8 PROPERTIES FOLDER "Plugins//DataModel")
		set_target_properties(datamodel_v8 PROPERTIES COMPILE_FLAGS "-DPLUMA_EXPORTS")
		set_target_properties(datamodel_v8 PROPERTIES LIBRARY_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/lib/plugins")
	else()
		list (APPEND USCXML_FILES ${V8_DATAMODEL})
		list (APPEND USCXML_OPT_LIBS ${V8_LIBRARY})
	endif()
endif()


if (LUA51_FOUND AND WITH_DM_LUA)
	set(USCXML_DATAMODELS "lua ${USCXML_DATAMODELS}")
	# Lua ecmascript datamodel
	file(GLOB LUA_DATAMODEL
		lua/*.cpp
		lua/*.h
	)
	if (BUILD_AS_PLUGINS)
		source_group("" FILES ${LUA_DATAMODEL})
		add_library(datamodel_lua SHARED ${LUA_DATAMODEL} "../Plugins.cpp")
		target_link_libraries(datamodel_lua 
			uscxml
			${LUA_LIBRARIES}
		)
		set_target_properties(datamodel_lua PROPERTIES FOLDER "Plugins//DataModel")
		set_target_properties(datamodel_lua PROPERTIES COMPILE_FLAGS "-DPLUMA_EXPORTS")
		set_target_properties(datamodel_lua PROPERTIES LIBRARY_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/lib/plugins")
	else()
		list (APPEND USCXML_FILES ${LUA_DATAMODEL})
		list (APPEND USCXML_OPT_LIBS ${LUA_LIBRARY})
	endif()
endif()

if (WITH_DM_C89)
	set(USCXML_DATAMODELS "c89 ${USCXML_DATAMODELS}")
	# Lua ecmascript datamodel
	file(GLOB_RECURSE C89_DATAMODEL
		c89/*.cpp
		c89/*.c
		c89/*.h
	)
	if (BUILD_AS_PLUGINS)
		source_group("" FILES ${C89_DATAMODEL})
		add_library(datamodel_c89 SHARED ${C89_DATAMODEL} "../Plugins.cpp")
		target_link_libraries(datamodel_c89 
			uscxml
		)
		set_target_properties(datamodel_c89 PROPERTIES FOLDER "Plugins//DataModel")
		set_target_properties(datamodel_c89 PROPERTIES COMPILE_FLAGS "-DPLUMA_EXPORTS")
		set_target_properties(datamodel_c89 PROPERTIES LIBRARY_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/lib/plugins")
	else()
		list (APPEND USCXML_FILES ${C89_DATAMODEL})
	endif()
endif()

if (WITH_DM_PROMELA)
	set(USCXML_DATAMODELS "promela ${USCXML_DATAMODELS}")
	# Lua ecmascript datamodel
	file(GLOB_RECURSE PROMELA_DATAMODEL
		promela/*.cpp
		promela/*.c
		promela/*.h
	)
	if (BUILD_AS_PLUGINS)
		source_group("" FILES ${PROMELA_DATAMODEL})
		add_library(datamodel_promela SHARED ${PROMELA_DATAMODEL} "../Plugins.cpp")
		target_link_libraries(datamodel_promela 
			uscxml
		)
		# SET_SOURCE_FILES_PROPERTIES is directory scope
		if (${CMAKE_CXX_COMPILER_ID} STREQUAL Clang)
			SET_SOURCE_FILES_PROPERTIES(promela/parser/promela.lex.yy.cpp PROPERTIES COMPILE_FLAGS -Wno-deprecated-register )
		endif()
		set_target_properties(datamodel_promela PROPERTIES FOLDER "Plugins//DataModel")
		set_target_properties(datamodel_promela PROPERTIES COMPILE_FLAGS "-DPLUMA_EXPORTS")
		set_target_properties(datamodel_promela PROPERTIES LIBRARY_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/lib/plugins")
	else()
		list (APPEND USCXML_FILES ${PROMELA_DATAMODEL})	
	endif()
endif()

if (NOT SWIG_FOUND)
	message(STATUS "No swig binary found, not generating DOM classes")		
elseif(SWIG_VERSION VERSION_LESS 3.0.8)
	message(STATUS "SWIG version > 3.0.8 is recommended, found ${SWIG_VERSION} - skipping DOM generation")
else()
	if (JSC_FOUND)
		add_custom_target(jsc-bindings
			COMMAND ${SWIG_EXECUTABLE}
			-I${XercesC_INCLUDE_DIRS}
			-I${PROJECT_SOURCE_DIR}/src
			-I${CMAKE_BINARY_DIR}
			-javascript 
			-jsc 
			-c++ 
			-o ${CMAKE_CURRENT_SOURCE_DIR}/ecmascript/JavaScriptCore/JSCDOM.cpp.inc
			ecmascript/JavaScriptCore/bindings.i
			WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
			COMMENT "Creating the DOM for JavaScriptCore ...")
		add_custom_target(jsc-bindings-noxercesc
			COMMAND ${SWIG_EXECUTABLE}
			-I${XercesC_INCLUDE_DIRS}
			-I${PROJECT_SOURCE_DIR}/src
			-I${CMAKE_BINARY_DIR}
			-javascript 
			-jsc
			-DNO_XERCESC
			-c++ 
			-o ${CMAKE_CURRENT_SOURCE_DIR}/ecmascript/JavaScriptCore/JSCEvent.cpp.inc
			ecmascript/JavaScriptCore/bindings.i
			WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
			COMMENT "Creating the DOM for JavaScriptCore (no XERCESC) ...")

		# list (APPEND JSC_DATAMODEL ${CMAKE_CURRENT_SOURCE_DIR}/ecmascript/JavaScriptCore/JSCDOM.cpp.inc)
		set_target_properties(jsc-bindings PROPERTIES FOLDER "Bindings")
	endif()

	if (V8_FOUND)
		add_custom_target(v8-bindings
			COMMAND ${SWIG_EXECUTABLE}
			-I${XercesC_INCLUDE_DIRS}
			-I${PROJECT_SOURCE_DIR}/src
			-I${CMAKE_BINARY_DIR}
			-javascript 
			-v8 
			-c++ 
			-o ${CMAKE_CURRENT_SOURCE_DIR}/ecmascript/v8/V8DOM.cpp.inc
			ecmascript/v8/bindings.i
			WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
			COMMENT "Creating the DOM for V8 ...")

		add_custom_target(v8-bindings-noxercesc
			COMMAND ${SWIG_EXECUTABLE}
			-I${XercesC_INCLUDE_DIRS}
			-I${PROJECT_SOURCE_DIR}/src
			-I${CMAKE_BINARY_DIR}
			-javascript 
			-v8 
			-DNO_XERCESC
			-c++ 
			-o ${CMAKE_CURRENT_SOURCE_DIR}/ecmascript/v8/V8Event.cpp.inc
			ecmascript/v8/bindings.i
			WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
			COMMENT "Creating the DOM for V8 (no XERCESC) ...")

		# list (APPEND V8_DATAMODEL ${CMAKE_CURRENT_SOURCE_DIR}/ecmascript/v8/V8DOM.cpp.inc)
		set_target_properties(v8-bindings PROPERTIES FOLDER "Bindings")
		
	endif()

	if (LUA51_FOUND)
		add_custom_target(lua-bindings
			COMMAND ${SWIG_EXECUTABLE}
			-I${XercesC_INCLUDE_DIRS}
			-I${PROJECT_SOURCE_DIR}/src
			-I${CMAKE_BINARY_DIR}
			-lua 
			-c++ 
			-o ${CMAKE_CURRENT_SOURCE_DIR}/lua/LuaDOM.cpp.inc
			lua/bindings.i
			WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
			COMMENT "Creating the DOM for Lua ...")

		add_custom_target(lua-bindings-noxercesc
			COMMAND ${SWIG_EXECUTABLE}
			-I${XercesC_INCLUDE_DIRS}
			-I${PROJECT_SOURCE_DIR}/src
			-I${CMAKE_BINARY_DIR}
			-lua 
			-DNO_XERCESC
			-c++ 
			-o ${CMAKE_CURRENT_SOURCE_DIR}/lua/LuaDOM.cpp.inc
			lua/bindings.i
			WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
			COMMENT "Creating the DOM for Lua ...")

		# list (APPEND V8_DATAMODEL ${CMAKE_CURRENT_SOURCE_DIR}/ecmascript/v8/V8DOM.cpp.inc)
		set_target_properties(lua-bindings PROPERTIES FOLDER "Bindings")		
	endif()
endif()



set(USCXML_INCLUDE_DIRS ${USCXML_INCLUDE_DIRS} PARENT_SCOPE)
set(USCXML_FILES ${USCXML_FILES} PARENT_SCOPE)
set(USCXML_DATAMODELS ${USCXML_DATAMODELS} PARENT_SCOPE)
