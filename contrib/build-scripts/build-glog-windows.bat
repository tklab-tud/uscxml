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
	set CPU_ARCH=x86_64
	goto :ARCH_FOUND
)

echo %LIB% |find "LIB;" > nul
if %errorlevel% == 0 (
	set DEST_DIR="%DIR%..\prebuilt\windows-x86/msvc"
	set CPU_ARCH=x86
	goto :ARCH_FOUND
)

:ARCH_FOUND

if "%DEST_DIR%" == "" (
	echo.
	echo Unknown Platform %Platform%.
	echo.
	goto :DONE
)

IF NOT EXIST "src\glog\log_severity.h" (
	echo.
	echo Cannot find src\glog\log_severity.h
	echo Run script from within glog directory:
	echo glog $ ..\%ME%
	echo.
	goto :DONE
)

devenv /upgrade google-glog.sln

if "%CPU_ARCH%" == "x86_64" (
	devenv /rebuild "debug|x64" google-glog.sln /project libglog_static
	devenv /rebuild "release|x64" google-glog.sln /project libglog_static
)

if "%CPU_ARCH%" == "x86" (
devenv /rebuild "debug|Win32" google-glog.sln /project libglog_static
devenv /rebuild "release|Win32" google-glog.sln /project libglog_static
)


echo.
echo If this failed, just add "typedef size_t ssize_t;" in logging.cc
echo.

copy Debug\libglog_static.lib %DEST_DIR%\lib\libglog_static_d.lib
copy Release\libglog_static.lib %DEST_DIR%\lib\libglog_static.lib
mkdir %DEST_DIR%\include\glog
xcopy src\windows\glog %DEST_DIR%\include /s /e


:DONE
pause