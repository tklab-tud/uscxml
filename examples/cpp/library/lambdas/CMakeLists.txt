cmake_minimum_required(VERSION 2.8.6)
project(lambda-scxml)

set(CMAKE_CXX_STANDARD 11)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "/usr/local/share/uscxml/cmake/")
find_package(USCXML REQUIRED)

# message(FATAL_ERROR "USCXML_LIBRARIES: ${USCXML_LIBRARIES}")


include_directories(${USCXML_INCLUDE_DIR})
add_executable(lambdas main.cpp)
target_link_libraries(lambdas ${USCXML_LIBRARIES})