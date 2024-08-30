@echo on
@rem Pushbutton installation of VeriFast dependencies.
@rem 
@rem WARNING: creates files/directories in c:\, such as c:\cygwin and c:\OCaml

@rem First, list pre-installed packages
c:\cygwin\bin\bash -lc "cygcheck -c -d" 

bitsadmin.exe /transfer "cygwin" https://www.cygwin.com/setup-x86_64.exe %TEMP%\setup-cygwin.exe || exit /b
%TEMP%\setup-cygwin.exe -B -qnNd -R c:/cygwin64 -l c:/cygwin64/var/cache/setup -s https://ftp.snt.utwente.nl/pub/software/cygwin/ -P p7zip -P cygutils-extra -P mingw64-x86_64-gcc-g++ -P make -P patch -P rlwrap -P libreadline6 -P diffutils -P wget -P cmake -P ninja || exit /b

@rem Add ",noacl" to prevent cygwin from messing with Windows file permissions
echo none /cygdrive cygdrive binary,posix=0,user,noacl 0 0 > c:\cygwin64\etc\fstab || exit /b

for /f "TOKENS=* USEBACKQ" %%f in (`cd`) do set VFWORKDIR=%%f

c:\cygwin64\bin\bash -lc "cd ""$VFWORKDIR"" && bash setup-windows.sh" || exit /b
