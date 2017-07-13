cmake_minimum_required(VERSION 2.8.6)
project(simple-scxml)

set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "/usr/local/share/uscxml/cmake/")
find_package(USCXML REQUIRED)


include_directories(${USCXML_INCLUDE_DIR})
add_executable(simple main.cpp)
target_link_libraries(simple ${USCXML_LIBRARIES})