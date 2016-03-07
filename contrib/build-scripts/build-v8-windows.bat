@ECHO off

set ME=%0
set DIR=%~dp0
set MSVC_VER=""
set DEPOT_TOOLS_WIN_TOOLCHAIN=0

if "%VSINSTALLDIR%" == "" (
	echo.
	echo %VSINSTALLDIR is not defined, run from within Visual Studio Command Prompt.
	echo.
	goto :DONE
)

cl.exe 2>&1 |findstr "Version\ 19.00" > nul
if %errorlevel% == 0 (
	set MSVC_VER=1900
  set GYP_MSVS_VERSION=2015
)

cl.exe 2>&1 |findstr "Version\ 18.00" > nul
if %errorlevel% == 0 (
	set MSVC_VER=1800
  set GYP_MSVS_VERSION=2013
)

cl.exe 2>&1 |findstr "Version\ 16.00" > nul
if %errorlevel% == 0 (
	set MSVC_VER=1600
  set GYP_MSVS_VERSION=2010
)

if [%MSVC_VER%] == [""] (
	echo.
	echo Unknown MSVC_VER %MSVC_VER%.
	echo.
	goto :DONE
)

echo %LIB% |find "LIB\amd64;" > nul
if %errorlevel% == 0 (
	set DEST_DIR="%DIR%..\prebuilt\windows-x86_64-msvc%MSVC_VER%"
	set CPU_ARCH=x86_64
	goto :ARCH_FOUND
)

echo %LIB% |find "LIB;" > nul
if %errorlevel% == 0 (
	set DEST_DIR="%DIR%..\prebuilt\windows-x86-msvc%MSVC_VER%"
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

IF NOT EXIST "src/v8.h" (
	echo.
	echo Cannot find src/v8.h
	echo Run script from within v8 directory:
	echo v8 $ %ME%
	echo.
	goto :DONE
)

echo.
echo Building with MCVC ver %MSVC_VER% for %CPU_ARCH% into %DEST_DIR%
echo.

if "%CPU_ARCH%" == "x86_64" (
  python build\gyp_v8 -Dtarget_arch=x64
  devenv /build Release build\All.sln

)

if "%CPU_ARCH%" == "x86" (
  python build\gyp_v8
)

:DONE
pause