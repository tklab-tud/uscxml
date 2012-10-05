cmake_minimum_required(VERSION 2.8.4)

project(uscxml)
enable_testing()

set(CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/contrib/cmake)

set(USCXML_LIBS)
set(USCXML_FILES)

# libxml2
find_package(LibXml2 REQUIRED)
include_directories(${LIBXML2_INCLUDE_DIR})
list (APPEND USCXML_LIBS ${LIBXML2_LIBRARIES})

# prefer rest as static libraries
set(CMAKE_FIND_LIBRARY_SUFFIXES .lib .a ${CMAKE_FIND_LIBRARY_SUFFIXES})

#glog
set(ENV{GLOG_SRC} ${CMAKE_SOURCE_DIR}/../glog)
find_package(GLOG REQUIRED)
include_directories(${GLOG_INCLUDE_DIR})
list (APPEND USCXML_LIBS ${GLOG_LIBRARY})

# arabica
find_package(Arabica REQUIRED)
include_directories(${ARABICA_INCLUDE_DIR})
list (APPEND USCXML_LIBS ${ARABICA_LIBRARY})

# boost - header only
FIND_PATH(Boost_INCLUDE_DIR boost/version.hpp PATHS /usr/include)
include_directories(${Boost_INCLUDE_DIR})

#event
set(ENV{EVENT_SRC} ${CMAKE_SOURCE_DIR}/../libevent)
find_package(EVENT REQUIRED)
include_directories(${EVENT_INCLUDE_DIR})
file(GLOB_RECURSE USCXML_IO_PROCESSOR_LIBEVENT
	src/uscxml/ioprocessor/basichttp/libevent/*.cpp
	src/uscxml/ioprocessor/basichttp/libevent/*.h
)
list (APPEND USCXML_FILES ${USCXML_IO_PROCESSOR_LIBEVENT})

file(GLOB_RECURSE USCXML_EVENTQUEUE_LIBEVENT
	src/uscxml/concurrency/eventqueue/libevent/*.cpp
	src/uscxml/concurrency/eventqueue/libevent/*.h
)
list (APPEND USCXML_FILES ${USCXML_EVENTQUEUE_LIBEVENT})

list (APPEND USCXML_LIBS ${EVENT_LIBRARY})

# v8
set(ENV{V8_SRC} ${CMAKE_SOURCE_DIR}/../v8)
find_package(V8 REQUIRED)
include_directories(${V8_INCLUDE_DIR})
file(GLOB_RECURSE USCXML_DATAMODEL_V8
	src/uscxml/datamodel/ecmascript/v8/*.cpp
	src/uscxml/datamodel/ecmascript/v8/*.h
)
list (APPEND USCXML_FILES ${USCXML_DATAMODEL_V8})
list (APPEND USCXML_LIBS ${V8_LIBRARY})

# curl
find_package(CURL REQUIRED)
include_directories(${CURL_INCLUDE_DIRS})
list (APPEND USCXML_LIBS ${CURL_LIBRARIES})

# umundo
find_package(UMUNDO REQUIRED)
include_directories(${UMUNDO_INCLUDE_DIR})
list (APPEND USCXML_LIBS ${UMUNDO_LIBRARIES})

# miles
find_package(MILES COMPONENTS core audio debug REQUIRED)
include_directories(${MILES_INCLUDE_DIR})
list (APPEND USCXML_LIBS ${MILES_LIBRARIES})

# openal
find_package(OpenAL REQUIRED)
include_directories(${OPENAL_INCLUDE_DIR})
list(APPEND USCXML_LIBS ${OPENAL_LIBRARY})


# the invokers for external services
file(GLOB_RECURSE USCXML_INVOKER src/uscxml/invoker/*.cpp src/uscxml/invoker/*.h)
list (APPEND USCXML_FILES ${USCXML_INVOKER})

# debug
file(GLOB_RECURSE USCXML_DEBUG src/uscxml/debug/*.cpp src/uscxml/debug/*.h)
list (APPEND USCXML_FILES ${USCXML_DEBUG})

file(GLOB USCXML_CONCURRENCY src/uscxml/concurrency/*.cpp src/uscxml/concurrency/*.h)
list (APPEND USCXML_FILES ${USCXML_CONCURRENCY})

file(GLOB USCXML_INTERPRETER src/uscxml/*.cpp src/uscxml/*.h)
list (APPEND USCXML_FILES ${USCXML_INTERPRETER})

include_directories(src)

# build library
add_library(uscxml ${USCXML_FILES})
target_link_libraries(uscxml ${USCXML_LIBS})

add_subdirectory(test)
add_subdirectory(src/bindings)

# ---- OLD DEPENDENCIES -------------

#set(Boost_DEBUG 1)
# find_package(Boost COMPONENTS thread regex system date_time REQUIRED)
# INCLUDE_DIRECTORIES(${Boost_INCLUDE_DIR})

#openssl - needed for pion
# find_package(OPENSSL REQUIRED)
# INCLUDE_DIRECTORIES(${OPENSSL_INCLUDE_DIR})

#zlib - needed for pion
# find_package(ZLIB REQUIRED)
# INCLUDE_DIRECTORIES(${ZLIB_INCLUDE_DIRS})

#iconv - needed for pion
# find_package(ICONV REQUIRED)
# INCLUDE_DIRECTORIES(${ICONV_INCLUDE_DIR})

#ev - no longer supported
# set(ENV{EV_SRC} ${CMAKE_SOURCE_DIR}/../libev)
# find_package(EV REQUIRED)
# include_directories(${EV_INCLUDE_DIR})

#pion
# set(ENV{PION_SRC} ${CMAKE_SOURCE_DIR}/../pion)
# find_package(PION REQUIRED)
# include_directories(${PION_INCLUDE_DIR})
# file(GLOB_RECURSE USCXML_IO_PROCESSOR_PION
# 	src/uscxml/ioprocessor/basichttp/pion/*.cpp
# 	src/uscxml/ioprocessor/basichttp/pion/*.h
# )

