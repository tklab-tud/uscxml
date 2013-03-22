# generate PHP module

find_package(PHP5)
if(PHP5_FOUND)
	include_directories(${PHP5_INCLUDE_PATH})
else()
	message(STATUS "No PHP5 libraries found - not building php module")
	return()
endif()

# copied from cmake's FindPHP4.cmake and adapted
if(APPLE)
	# this is a hack for now
  set(PHP_MODULE_CXX_FLAGS "${CMAKE_SHARED_MODULE_CREATE_CXX_FLAGS} -Wl,-flat_namespace")
  foreach(symbol
		__efree
		__emalloc
		__estrdup
		__estrndup
		__object_init
		__object_init_ex
		__zend_get_parameters_array_ex
		__zend_list_find
		__zval_copy_ctor
		__zval_copy_ctor_func
		_add_property_zval_ex
		_alloc_globals
		_compiler_globals
		_convert_to_double
		_convert_to_long
		_convert_to_boolean
		__convert_to_string
		_gc_remove_zval_from_buffer
		_call_user_function
		_executor_globals
		_zend_get_constant
		_zend_lookup_class
		_zend_register_long_constant
		_zval_is_true
		_zend_error
		_zend_hash_find
		__zend_hash_add_or_update
		_zend_register_internal_class_ex
		_zend_register_list_destructors_ex
		_zend_register_resource
		_zend_rsrc_list_get_rsrc_type
		_zend_wrong_param_count
		_zval_used_for_init
		)
    set(PHP_MODULE_CXX_FLAGS
      "${PHP_MODULE_CXX_FLAGS},-U,${symbol}")
  endforeach()
endif()

#message(FATAL_ERROR "PHP_LDFLAGS: ${PHP_LDFLAGS}")

include_directories(${CMAKE_CURRENT_SOURCE_DIR})
include_directories(${PHP_INCLUDE_DIRS})

SET(CMAKE_SWIG_FLAGS "")

# we need ; to produce a space with the package .. weird
SET_SOURCE_FILES_PROPERTIES(uscxml.i PROPERTIES CPLUSPLUS ON)

SWIG_ADD_MODULE(uscxmlNativePHP php5 uscxml.i)
foreach(PHP_LIBRARY ${PHP_LIBRARIES})
	SWIG_LINK_LIBRARIES(uscxmlNativePHP ${PHP_LIBRARY})
endforeach()

if (APPLE)
	set_target_properties(uscxmlNativePHP PROPERTIES LINK_FLAGS ${PHP_MODULE_CXX_FLAGS})
endif()
#set_target_properties(uscxmlNativePHP PROPERTIES LINK_FLAGS ${PHP_LDFLAGS})

set_target_properties(uscxmlNativePHP PROPERTIES FOLDER "Bindings")

SWIG_LINK_LIBRARIES(uscxmlNativePHP uscxml)
