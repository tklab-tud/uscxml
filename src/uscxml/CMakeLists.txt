############################################################
# Actual files of core library
############################################################

file(GLOB_RECURSE USCXML_SERVER
	src/uscxml/server/*.cpp
	src/uscxml/server/*.h
)
source_group("Interpreter" FILES ${USCXML_SERVER})
list (APPEND USCXML_FILES ${USCXML_SERVER})

file(GLOB_RECURSE USCXML_CONCURRENCY
	src/uscxml/concurrency/*.cpp
	src/uscxml/concurrency/*.h
)
source_group("Interpreter" FILES ${USCXML_CONCURRENCY})
list (APPEND USCXML_FILES ${USCXML_CONCURRENCY})

file(GLOB_RECURSE USCXML_DEBUG
	src/uscxml/debug/*.cpp
	src/uscxml/debug/*.h
)
source_group("Interpreter" FILES ${USCXML_DEBUG})
list (APPEND USCXML_FILES ${USCXML_DEBUG})

file(GLOB_RECURSE USCXML_INTERPRETERS
	src/uscxml/interpreter/*.cpp
	src/uscxml/interpreter/*.h
)
source_group("Interpreter" FILES ${USCXML_INTERPRETERS})
list (APPEND USCXML_FILES ${USCXML_INTERPRETERS})

file(GLOB USCXML_CORE
	${CMAKE_SOURCE_DIR}/contrib/src/jsmn/jsmn.c
	src/uscxml/*.cpp
	src/uscxml/*.h
)
source_group("Interpreter" FILES ${USCXML_CORE})
list (APPEND USCXML_FILES ${USCXML_CORE})

if (BUILD_AS_PLUGINS)
	list (APPEND USCXML_INCLUDE_DIRS ${PROJECT_SOURCE_DIR}/src/uscxml/plugins)
	file(GLOB PLUMA 
		src/uscxml/plugins/Pluma/*.cpp 
		src/uscxml/plugins/Pluma/*.h
		src/uscxml/plugins/*.cpp 
		src/uscxml/plugins/*.h
	)
	source_group("Interpreter" FILES ${PLUMA})
	list (APPEND USCXML_FILES ${PLUMA})
	add_definitions("-DBUILD_AS_PLUGINS")
endif()

include(src/uscxml/plugins/datamodel/CMakeLists.txt)
include(src/uscxml/plugins/element/CMakeLists.txt)
include(src/uscxml/plugins/invoker/CMakeLists.txt)
include(src/uscxml/plugins/ioprocessor/CMakeLists.txt)

