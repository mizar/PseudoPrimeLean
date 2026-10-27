@echo off
setlocal

set "MSYS2_CLANG64=%USERPROFILE%\scoop\apps\msys2\current\clang64"
set "PATH=%MSYS2_CLANG64%\bin;%PATH%"

"%MSYS2_CLANG64%\bin\clang++.exe" %* -static
exit /b %ERRORLEVEL%
