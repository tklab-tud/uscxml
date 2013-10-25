@ECHO off

set ME=%0
set DIR=%~dp0

if "%VSINSTALLDIR%" == "" (
	echo.
	echo %VSINSTALLDIR is not defined, run from within Visual Studio Command Prompt.
	echo.
	goto :DONE
)

echo %LIB% |find "LIB\amd64;" > nul
if %errorlevel% == 0 (
	set DEST_DIR="%DIR%..\prebuilt\windows-x86_64/msvc"
	goto :ARCH_FOUND
)

echo %LIB% |find "LIB;" > nul
if %errorlevel% == 0 (
	set DEST_DIR="%DIR%..\prebuilt\windows-x86/msvc"
	goto :ARCH_FOUND
)

:ARCH_FOUND

if "%DEST_DIR%" == "" (
	echo.
	echo Unknown Platform %Platform%.
	echo.
	goto :DONE
)

IF NOT EXIST "event.c" (
	echo.
	echo Cannot find event.c
	echo Run script from within libevent directory:
	echo libevent $ ..\%ME%
	echo.
	goto :DONE
)

nmake -f Makefile.nmake clean
nmake -f Makefile.nmake

copy libevent_core.lib %DEST_DIR%\lib
copy libevent_extras.lib %DEST_DIR%\lib
copy libevent.lib %DEST_DIR%\lib

:DONE
pause