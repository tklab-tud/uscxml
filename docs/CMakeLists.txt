############################################################
# Build documentation
############################################################

# see https://tty1.net/blog/2014/cmake-doxygen_en.html
find_package(Doxygen)
option(BUILD_DOCS "Create API documentation (requires doxygen)" ${DOXYGEN_FOUND})

if(BUILD_DOCS)
	configure_file(
		${CMAKE_CURRENT_SOURCE_DIR}/Doxyfile.in 
		${CMAKE_CURRENT_BINARY_DIR}/Doxyfile 
		@ONLY)

	add_custom_target(docs
	    COMMAND ${DOXYGEN_EXECUTABLE} ${CMAKE_CURRENT_BINARY_DIR}/Doxyfile
	    WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
	    COMMENT "Generating API documentation with Doxygen"
	    VERBATIM)
	
	file(MAKE_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/html)
	
	install(DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/html DESTINATION share/doc/uscxml)
endif()
