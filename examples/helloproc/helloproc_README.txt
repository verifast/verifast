Helloproc README
=============

Welcome to Helloproc, an example verified Linux kernel module using
the VeriFast Linux Kernel Module Verification Kit.

Helloproc creates a virtual file (/proc/helloproc/value), which contains
a text, including the number of times the file is read.


How to build and verify
=======================

Both build and verify
---------------------
Just type "make" in the directory where helloproc is located.
This will first verify helloproc and then build a kernel module you can
load in your kernel.

For building the kernel module, you need the Linux header files
(not needed for verification).  They are normally shipped as a
package with your Linux distribution, e.g. linux-headers-generic
or linux-headers-2.6-486.  The Linux headers have to match the
architecture and Linux version you want to compile for.

Only verify
-----------
Just type "make verify_only".

Alternatively you can use helloproc.mysh, read that file for more information.


Files
=====
-   helloproc_main.c
    The sourcecode of helloproc (only one file).

-   Makefile
    The configuration for building and verifying helloproc.

-   helloproc.mysh
    Alternative verification launcher.

