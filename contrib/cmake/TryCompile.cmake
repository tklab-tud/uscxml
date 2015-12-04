include(CheckCXXSourceCompiles)
# set(CMAKE_REQUIRED_INCLUDES ${SWI_INCLUDE_DIR} ${SWI_CPP_INCLUDE_DIR})
# set(CMAKE_REQUIRED_LIBRARIES ${SWI_LIBRARY})

check_cxx_source_compiles("
	#include <typeinfo>
	#include <execinfo.h>
	#include <dlfcn.h>
	extern \"C\"
	void __cxa_throw (void *thrown_exception, void *pvtinfo, void (*dest)(void *)) {
	}
	int main() {}
" CXA_THROW_HAS_VOID_PVTINFO_TYPE)

check_cxx_source_compiles("
	#include <typeinfo>
	#include <execinfo.h>
	#include <dlfcn.h>
	extern \"C\"
	void __cxa_throw (void *thrown_exception, std::type_info *pvtinfo, void (*dest)(void *)) {
	}
	int main() {}
" CXA_THROW_HAS_TYPEINFO_PVTINFO_TYPE)
