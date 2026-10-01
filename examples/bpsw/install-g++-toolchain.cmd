@echo off
setlocal

set "BPSW_MSYS2_ROOT=%USERPROFILE%\scoop\apps\msys2\current"
if not exist "%BPSW_MSYS2_ROOT%\usr\bin\bash.exe" (
  echo MSYS2 was not found at "%BPSW_MSYS2_ROOT%". 1>&2
  echo Install MSYS2 first, or edit BPSW_MSYS2_ROOT in this script. 1>&2
  exit /b 1
)

set "MSYSTEM=MINGW64"
"%BPSW_MSYS2_ROOT%\usr\bin\bash.exe" --login -c "pacman -Syu --needed --noconfirm mingw-w64-x86_64-toolchain mingw-w64-x86_64-boost"
exit /b %ERRORLEVEL%
