Building VeriFast on Windows
============================

Note: binary downloads are available, both ["nightly" builds](https://github.com/verifast/verifast#binaries) of the latest commit, and binaries for [named releases](https://github.com/verifast/verifast/releases).

Note: The instructions below may get out of date. When that happens, please submit an issue. In the meantime, guaranteed up-to-date instructions can be found by looking at the script, [appveyor.yml](https://github.com/verifast/verifast/blob/master/appveyor.yml), used by the AppVeyor CI service that automatically builds and tests VeriFast after each commit. This script first runs the command listed below `install:`, and then the command listed below `build_script:`.

Dependencies
------------
Install [Visual Studio 2019 Community](https://visualstudio.microsoft.com/vs/community/): 
- Manually: Download `Visual Studio`. In the installer, choose Desktop development using C++. You only need VC++, the Windows 10 SDK, and the CMake tools. 
- PowerShell: use the [MSVC installation script](msvc_install.ps1) to automatically install `Visual Studio` with the required components:
  ```PowerShell
  powershell.exe -ExecutionPolicy RemoteSigned -File .\msvc_install.ps1 -install_dir *path_to_install_msvc*
  ```
  The `-install_dir` argument is optional and specifies where `Visual Studio` should be installed to. The script will install it to `C:\vfMSVC` by default if the argument is omitted.

  If you run the script from a command prompt without administrator privileges, a prompt may ask you to confirm the installation.

  The installation script may ask to reboot your system in order to complete the installation. You can rerun the script afterwards to confirm that the installation completed successfully.

The next step requires that `vcvarsall.bat` is present in you PATH, which can be found in `path-to-msvc-installation-directory\VC\Auxiliary\Build`. E.g.:
```
set PATH=C:\vfMSVC\VC\Auxiliary\Build;%PATH%
```
This batch file sets various environment variables in order to compile C++ code with MSVC.

To install the software needed to build VeriFast, run [setup-windows.bat](https://github.com/verifast/verifast/blob/master/setup-windows.bat). This script does the following:

- It installs Cygwin (32-bit) and the Cygwin packages `p7zip`, `cygutils-extra`, `make`, `mingw64-i686-gcc-g++`, `mingw64-i686-gcc-core`, `mingw64-i686-gcc`, `patch`, `rlwrap`, `libreadline6`, `diffutils`, `mingw64-i686-binutils`, and `wget`.
- It prevents Cygwin from messing with Windows file permissions by adding a line to Cygwin's `/etc/fstab`:
  ```
  echo none /cygdrive cygdrive binary,posix=0,user,noacl 0 0 > c:\cygwin\etc\fstab
  ```
- It calls `vcvarsall.bat` to set the environment to configure the command line for native compilation.
- Inside a Cygwin Bash shell, it runs [setup-windows.sh](https://github.com/verifast/verifast/blob/master/setup-windows.sh), which installs the following dependencies:
  - LLVM/Clang 13.0.0 (a language front-end and tooling infrastructure for languages in the C language family)
  - OCaml 4.13.0
  - Findlib 1.9.1 (for the `ocamlfind` tool, used by Z3's install script and dune)
  - OCaml-Num 1.4 (arbitrary-precision arithmetic)
  - Ocamlbuild 0.14.0 (to build Camlp4)
  - Camlp4 4.13+1 (an OCaml preprocessor, for the streams notation used in VeriFast's parser)
  - GTK+ (a cross-platform GUI toolkit)
  - Lablgtk 2.18.11 (OCaml bindings to GTK+)
  - Z3 4.8.5 (a powerful theorem prover, including OCaml bindings)
  - Dune 2.9.1 (to build and install other OCaml dependencies)
  - Cap'n Proto 0.9.1 (fast data interchange format)
  - Capnp 3.4.0 (OCaml plugin for Cap'n Proto)
  - Other dependencies, mainly to support Capnp:
    - Csexp 1.5.1
    - Sexplib0 0.14.0
    - Base 0.14.1
    - Res 5.0.1
    - Stdio 0.14.0
    - Cppo 1.6.8
    - Ocplib-endian 1.1
    - Stdint 0.7.0
    - Result 1.5
  
  It does so by downloading a [llvm-clang_windows-latest](https://github.com/NielsMommen/vf-llvm-clang-build/releases/tag/v1.0.0) and [VFDeps](https://github.com/verifast/vfdeps-win) package with pre-compiled versions of these dependencies. To see which version is currently being used, see [setup-windows.sh](https://github.com/verifast/verifast/blob/master/setup-windows.sh). Note: these binaries are location-dependent. They need to be below `C:\llvm-clang_windows-latest` and `C:\vfdeps`; that is, extract the archives into `C:\`.

Building VeriFast
-----------------

To build VeriFast:
1. Open a Cygwin terminal.
2. `cd /cygdrive/c/my-path-to-verifast/src`
3. Make sure all dependencies are in your `PATH`. For example: `export PATH="/cygdrive/c/vfdeps/bin:$PATH"`.
5. Tell the VeriFast build script where the GTK+ binaries are: `export GTK=/cygdrive/c/vfdeps`.
6. `make`
