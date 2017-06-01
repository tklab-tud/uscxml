# generate JNI library and create a jar
# Make from within Eclipse fails miserably with the whole thing

find_package(Lua)
if (LUA_FOUND)
	include_directories(${LUA_INCLUDE_DIR})
else()
	message(STATUS "No Lua headers found - not building Lua wrappers")
	return()
endif()

include_directories(${CMAKE_CURRENT_SOURCE_DIR})

SET(CMAKE_SWIG_FLAGS "")
SET(USCXML_LUA_DIR "uscxml")

# we need ; to produce a space with the package .. weird
SET_SOURCE_FILES_PROPERTIES(uscxml.i PROPERTIES SWIG_FLAGS "-w473")
SET_SOURCE_FILES_PROPERTIES(uscxml.i PROPERTIES CPLUSPLUS ON)
SET(CMAKE_SWIG_OUTDIR "${CMAKE_CURRENT_BINARY_DIR}/${USCXML_LUA_DIR}")

SWIG_ADD_MODULE(uscxmlNativeLua lua uscxml.i)
foreach(LUA_LIBRARY ${LUA_LIBRARIES})
	SWIG_LINK_LIBRARIES(uscxmlNativeLua ${LUA_LIBRARY})
endforeach()
set_target_properties(uscxmlNativeLua PROPERTIES FOLDER "Bindings")
set_target_properties(uscxmlNativeLua PROPERTIES COMPILE_FLAGS "-DSWIG")

swig_link_libraries(uscxmlNativeLua uscxml)

set(USCXML_LANGUAGE_BINDINGS "lua ${USCXML_LANGUAGE_BINDINGS}")
set(USCXML_LANGUAGE_BINDINGS ${USCXML_LANGUAGE_BINDINGS} PARENT_SCOPE)
