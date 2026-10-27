@echo off
setlocal

set "MSYS2_MINGW64=%USERPROFILE%\scoop\apps\msys2\current\mingw64"
set "PATH=%MSYS2_MINGW64%\bin;%PATH%"

"%MSYS2_MINGW64%\bin\g++.exe" %* -static
exit /b %ERRORLEVEL%
