@echo on
@rem Pushbutton installation of VeriFast dependencies.
@rem 
@rem WARNING: creates files/directories in c:\, such as c:\cygwin and c:\OCaml
@rem Assumes VeriFast is in c:\projects\verifast

@rem First, list pre-installed packages
c:\cygwin\bin\bash -lc "cygcheck -c -d" 

bitsadmin.exe /transfer "cygwin" https://cygwin.com/setup-x86.exe %TEMP%\setup-cygwin-x86.exe || exit /b
%TEMP%\setup-cygwin-x86.exe -B -qnNd -R c:/cygwin -l c:/cygwin/var/cache/setup -s http://ftp.inf.tu-dresden.de/software/windows/cygwin32/ -P p7zip -P cygutils-extra -P make -P mingw64-i686-gcc-g++ -P mingw64-i686-gcc-core -P mingw64-i686-gcc -P patch -P rlwrap -P libreadline6 -P diffutils -P mingw64-i686-binutils || exit /b
@rem Package 'wget' is required as well but is pre-installed on AppVeyor.

@rem Add ",noacl" to prevent cygwin from messing with Windows file permissions
echo none /cygdrive cygdrive binary,posix=0,user,noacl 0 0 > c:\cygwin\etc\fstab || exit /b

c:\cygwin\bin\bash -lc "cd /cygdrive/c/projects/verifast && bash setup-windows.sh" || exit /b
