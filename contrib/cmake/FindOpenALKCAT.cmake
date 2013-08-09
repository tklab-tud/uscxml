SET(WIN_DIRECTORIES "")
if(CMAKE_SIZEOF_VOID_P EQUAL 8)
	list(APPEND WIN_DIRECTORIES "C:/Program Files/openal-soft-1.15.1-bin/lib/Win64")
else()
	list(APPEND WIN_DIRECTORIES "C:/Program Files/openal-soft-1.15.1-bin/lib/Win32")
endif()

find_path(OPENAL_INCLUDE_DIR al.h
  HINTS
    ENV OPENALDIR
  PATH_SUFFIXES include/AL include/OpenAL include
  PATHS
	"C:/Program Files/openal-soft-1.15.1-bin"
)

find_library(OPENAL_LIBRARY
  NAMES OpenAL libOpenAL32.dll libOpenAL64.dll
  HINTS
    ENV OPENALDIR
  PATH_SUFFIXES lib64 lib libs64 libs libs/Win32 libs/Win64
  PATHS
	${WIN_DIRECTORIES}
)


# handle the QUIETLY and REQUIRED arguments and set OPENAL_FOUND to TRUE if
# all listed variables are TRUE
INCLUDE(FindPackageHandleStandardArgs)
FIND_PACKAGE_HANDLE_STANDARD_ARGS(OpenAL  DEFAULT_MSG  OPENAL_LIBRARY OPENAL_INCLUDE_DIR)

mark_as_advanced(OPENAL_LIBRARY OPENAL_INCLUDE_DIR)
