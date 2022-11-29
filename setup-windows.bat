@echo on
@rem Pushbutton installation of VeriFast dependencies.
@rem 
@rem WARNING: creates files/directories in c:\, such as c:\cygwin and c:\OCaml

@rem First, list pre-installed packages
c:\cygwin\bin\bash -lc "cygcheck -c -d" 

bitsadmin.exe /transfer "cygwin" https://cygwin.com/setup.exe %TEMP%\setup-cygwin.exe || exit /b
%TEMP%\setup-cygwin.exe -B -qnNd -R c:/cygwin -l c:/cygwin/var/cache/setup -s http://ftp.inf.tu-dresden.de/software/windows/cygwin32/ -P p7zip -P cygutils-extra -P make -P mingw64-i686-gcc-g++ -P mingw64-i686-gcc-core -P mingw64-i686-gcc -P patch -P rlwrap -P libreadline6 -P diffutils -P mingw64-i686-binutils -P wget || exit /b

@rem Add ",noacl" to prevent cygwin from messing with Windows file permissions
echo none /cygdrive cygdrive binary,posix=0,user,noacl 0 0 > c:\cygwin\etc\fstab || exit /b

for /f "TOKENS=* USEBACKQ" %%f in (`cd`) do set VFWORKDIR=%%f

@rem set MSVC environment variables
call vcvarsall.bat x86

c:\cygwin\bin\bash -lc "cd ""$VFWORKDIR"" && bash setup-windows.sh" || exit /b