@rem Pushbutton installation of VeriFast dependencies.
@rem (no z3, no vfide)
@rem WARNING: writes to c:\cygwin and c:\OCaml
@rem Assumes VeriFast is in c:\projects\verifast

bitsadmin.exe /transfer "cygwin" https://cygwin.com/setup-x86.exe %TEMP%\setup-cygwin-x86.exe
%TEMP%\setup-cygwin-x86.exe -B -qnNd -R c:/cygwin -l c:/cygwin/var/cache/setup -s http://ftp.inf.tu-dresden.de/software/windows/cygwin32/ -P p7zip curl -P make -P mingw64-i686-gcc-g++ -P mingw64-i686-gcc-core -P mingw64-i686-gcc -P patch -P rlwrap -P libreadline6 -P diffutils -P wget

c:/cygwin/bin/bash -lc "cd /cygdrive/c/projects/verifast && bash setup-windows.sh"
