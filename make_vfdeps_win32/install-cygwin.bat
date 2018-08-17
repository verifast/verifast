@echo on


bitsadmin.exe /transfer "cygwin" https://cygwin.com/setup-x86.exe C:\Bart\setup-cygwin-x86.exe || exit /b


C:\Bart\setup-cygwin-x86.exe -B -qnNd -R c:/cygwin -l c:/cygwin/var/cache/setup -s http://ftp.inf.tu-dresden.de/software/windows/cygwin32/ -P python -P p7zip -P curl -P m4 -P make -P mingw64-i686-gcc-g++ -P mingw64-i686-gcc-core -P mingw64-i686-gcc -P patch -P rlwrap -P libreadline6 -P diffutils -P dos2unix -P mingw64-i686-binutils || exit /b


@rem Package 'wget' is required as well but is pre-installed on AppVeyor.



@rem Add ",noacl" to prevent cygwin from messing with Windows file permissions


echo none /cygdrive cygdrive binary,posix=0,user,noacl 0 0 > c:\cygwin\etc\fstab || exit /b



rem c:\cygwin\bin\bash -lc "cd /cygdrive/c/projects/verifast && bash setup-windows.sh" || exit /b

