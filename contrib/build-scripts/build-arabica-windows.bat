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

IF NOT EXIST "src\arabica.cpp" (
	echo.
	echo Cannot find src\arabica.cpp
	echo Run script from within arabica directory:
	echo arabica $ ..\%ME%
	echo.
	goto :DONE
)

devenv /upgrade vs10/Arabica.sln

if "%CPU_ARCH%" == "x86_64" (
	devenv /build "debug|x64" vs10/Arabica.sln /project ArabicaLib
	devenv /build "release|x64" vs10/Arabica.sln /project ArabicaLib
)

if "%CPU_ARCH%" == "x86" (
	devenv /build "debug|Win32" vs10/Arabica.sln /project ArabicaLib
	devenv /build "release|Win32" vs10/Arabica.sln /project ArabicaLib
)

copy lib\Arabica-debug.lib %DEST_DIR%\lib\Arabica_d.lib
copy lib\Arabica.lib %DEST_DIR%\lib\Arabica.lib
mkdir %DEST_DIR%\include\arabica
xcopy include\*.hpp %DEST_DIR%\include\arabica /s /e


:DONE
pause