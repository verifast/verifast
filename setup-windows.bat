@rem Pushbutton installation of VeriFast dependencies.
@rem 
@rem WARNING: creates files/directories in c:\, such as c:\cygwin and c:\OCaml
@rem Assumes VeriFast is in c:\projects\verifast

bitsadmin.exe /transfer "cygwin" https://cygwin.com/setup-x86.exe %TEMP%\setup-cygwin-x86.exe
%TEMP%\setup-cygwin-x86.exe -B -qnNd -R c:/cygwin -l c:/cygwin/var/cache/setup -s http://ftp.inf.tu-dresden.de/software/windows/cygwin32/ -P p7zip curl -P make -P mingw64-i686-gcc-g++ -P mingw64-i686-gcc-core -P mingw64-i686-gcc -P patch -P rlwrap -P libreadline6 -P diffutils -P wget -P dos2unix -P mingw64-i686-binutils

@rem Add ",noacl" to prevent cygwin from messing with Windows file permissions
echo none /cygdrive cygdrive binary,posix=0,user,noacl 0 0 > c:\cygwin\etc\fstab

c:\cygwin\bin\bash -lc "cd /cygdrive/c/projects/verifast && bash setup-windows.sh"
copy /y c:\gtk\bin\zlib1.dll c:\projects\verifast\bin
