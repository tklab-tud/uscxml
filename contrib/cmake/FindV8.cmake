FIND_PATH(V8_INCLUDE_DIR v8.h
  PATH_SUFFIXES include
  PATHS
  /usr/local
  /usr
  /sw # Fink
  /opt/local # DarwinPorts
  /opt/csw # Blastwave
  /opt
  HINTS $ENV{V8_SRC}
)

FIND_LIBRARY(V8_LIBRARY_BASE_RELEASE
  NAMES v8_base v8
  HINTS $ENV{V8_SRC}/out/native/
)
if (V8_LIBRARY_BASE_RELEASE)
	list(APPEND V8_LIBRARY optimized ${V8_LIBRARY_BASE_RELEASE})
endif()

FIND_LIBRARY(V8_LIBRARY_SNAPSHOT_RELEASE
  NAMES v8_snapshot
  HINTS $ENV{V8_SRC}/out/native/
)
if (V8_LIBRARY_SNAPSHOT_RELEASE)
	list(APPEND V8_LIBRARY optimized ${V8_LIBRARY_SNAPSHOT_RELEASE})
endif()

FIND_LIBRARY(V8_LIBRARY_BASE_DEBUG
  NAMES v8_base_d v8_d v8_base_g v8_g
  HINTS $ENV{V8_SRC}/out/native/
)
if (V8_LIBRARY_BASE_DEBUG)
	list(APPEND V8_LIBRARY debug ${V8_LIBRARY_BASE_DEBUG})
else()
	if (UNIX)
		list(APPEND V8_LIBRARY debug ${V8_LIBRARY_BASE_RELEASE})
	endif()
endif()

FIND_LIBRARY(V8_LIBRARY_SNAPSHOT_DEBUG
	NAMES v8_snapshot_d
	HINTS $ENV{V8_SRC}/out/native/
)
if (V8_LIBRARY_SNAPSHOT_DEBUG)
	list(APPEND V8_LIBRARY debug ${V8_LIBRARY_SNAPSHOT_DEBUG})
else()
	if (UNIX AND V8_LIBRARY_SNAPSHOT_RELEASE)
		list(APPEND V8_LIBRARY debug ${V8_LIBRARY_SNAPSHOT_RELEASE})
	endif()
endif()

# I have no idea how we would find the version otherwise :(
if (V8_LIBRARY AND V8_INCLUDE_DIR)
	include(CheckCXXSourceCompiles)
	set(CMAKE_REQUIRED_INCLUDES ${V8_INCLUDE_DIR})
	set(CMAKE_REQUIRED_LIBRARIES ${V8_LIBRARY})
	check_cxx_source_compiles("
		#include <v8.h>
		int main(){ 
			v8::Locker locker;
			v8::HandleScope scope;
			v8::Local<v8::ObjectTemplate> global = v8::ObjectTemplate::New();
			v8::Persistent<v8::Context> context = v8::Context::New(0, global);
			v8::Context::Scope contextScope(context);
		}" V8_VER_COMPILES_AS_031405)

	if (NOT V8_VER_COMPILES_AS_031405)
		check_cxx_source_compiles("
			#include <v8.h>
			int main(){ 
				v8::Local<v8::Value> foo = v8::Array::New(v8::Isolate::GetCurrent()); 
			}" V8_VER_COMPILES_AS_032317)

		if (NOT V8_VER_COMPILES_AS_032317)
			message(STATUS "Your V8 installation is unsupported - we support 3.14.5 and 3.23.17")
			unset(V8_LIBRARY)
			unset(V8_INCLUDE_DIR)
		else()
			set(V8_VERSION "032317")
		endif()
	else()
		set(V8_VERSION "031405")
	endif()
endif()

INCLUDE(FindPackageHandleStandardArgs)
FIND_PACKAGE_HANDLE_STANDARD_ARGS(V8 DEFAULT_MSG V8_LIBRARY V8_INCLUDE_DIR)
MARK_AS_ADVANCED(V8_LIBRARY V8_INCLUDE_DIR)
