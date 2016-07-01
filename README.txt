Welcome to the VeriFast codebase!
=================================

Map of the codebase
-------------------

testsuite.mysh
    The test suite. Should cover all features. When you commit a change,
    please add a test case to the test suite that tests your change. This also
    serves as useful documentation for your change and makes it easier to
    audit your commit.
    Note: test cases that work with both Z3 and Redux should start with
    'verifast_both'. Test cases that work only with Z3 should start with
    'ifnotmac verifast'. Test cases that work only with Redux should start
    with 'verifast -prover redux'.
src -- The source code (written in OCaml)
    generate_vfversion.ml
        A build-time utility that generates vfversion.ml containing the
        current date.

    plugins.ml, plugins_private.ml, plugins2.ml
        Preliminary support for logic plugins (not to be confused with prover
        plugins). See examples/plugin/.
    DynType.ml
        Implements safe dynamic typecasts in OCaml
    proverapi.ml
        Abstract interface between SMT solvers and VeriFast
    z3prover.ml
        Implements the prover API using the Z3 SMT solver
    simplex.ml
        A decision procedure for linear rational arithmetic; used by Redux
    redux.ml
        The Redux SMT solver; a modified partial implementation of the
        Simplify technical report by Detlefs, Nelson, et al. Sometimes
        faster than Z3. Also useful on platforms where no Z3 binary is
        available (like MacOS).
    verifast.ml
        The core module; performs the actual verification.
        *See extra info at the top of verifast.ml!*
    verifastPluginZ3.ml
        Registers the Z3 proverapi implementation as a prover plugin with
        VeriFast. (OCaml modules can contain toplevel code. On program startup
        all toplevel code of all modules is executed in the order in which the
        modules appear in the compiler command line that was used to build the
        executable.)
    verifastPluginRedux.ml
        Registers the Redux proverapi implementation as a prover plugin with
        VeriFast
    vfconsole.ml
        The main module for the VeriFast command-line tool
    Fonts_default.ml
        VeriFast IDE configuration values, such as the default font name
    Fonts_mac.ml
        VeriFast IDE configuration values for MacOS
    vfide.ml
        The main module for the VeriFast IDE

    dlsymtool.ml
        Tool for generating stub files and manifests for DLL scenarios. See
        the BeepDriver and MockKernel examples

    mysh.ml
        A very simple script runner. Used to run the test suite. The
        executable ships with the VeriFast release.

    vfstrip.ml
        Tool that takes a C or Java source file with VeriFast annotations
        on standard input and outputs a version without annotations. Used to
        generate the files in tutorial/ from the files in tutorial_solutions/.

    Makefile
        The makefile for Windows builds (for use by NMAKE, Microsoft's make
        utility that ships with Visual Studio).
        The default target builds bin/verifast.exe and bin/vfide.exe and
        runs the test suite.
    GNUmakefile
        The makefile for Linux and MacOS builds (for use by GNU make).
        The default target builds bin/verifast and bin/vfide and runs the
        test suite.

    mvf.bat
        Shorthand for 'nmake ..\bin\verifast.exe'
        Note: you should usually just type 'nmake'.
    mide.bat
        Shorthand for 'nmake ..\bin\vfide.exe'
        Note: you should usually just type 'nmake'.
bin
    Contains files that will ship in the release. Most of these are
    described in examples/index.html.
doc/tutorial
    The VeriFast tutorial
examples
    The source files used by the test suite. Contains mostly small test cases
    but also a few larger examples. See examples/index.html for descriptions.
    These ship with the release.
    java
        Java test cases and examples
help
    HTML documents that ship with the release and that are launched by the
    VeriFast IDE when the user clicks on the question mark button in the
    error message bar.
tests/errors
    Some negative test cases. These test that VeriFast doesn't simply always
    report "0 errors found". Uses VeriFast's should_fail feature.
    Specifically, if a source line has a comment of the form //~ on it,
    VeriFast remembers that line number as a should_fail line. If VeriFast
    subsequently detects an error on that line, it does not report it.
    On the other hand, if VeriFast does not detect an error on that line,
    it reports a should_fail error.

How to build
------------

See the appropriate README.xyz.md file for your platform.

Commit guidelines
-----------------
- Please always add a test case for your change.
- Please always build and run the test suite before committing.
- Please review your diffs before committing. In the TortoiseSVN commit
  dialog, right-click on a modified file to see a diff. In the TortoiseSVN
  diff viewer, you can easily revert spurious diff lines (with e.g. just
  whitespace changes) by right-clicking on the diff line.
- Keep your checkout clean so that you can easily spot unversioned files
  that you need to svn add.
- Adhere to the existing coding style. When inserting code, mimic the
  style of the surrounding code.

How to understand the codebase
------------------------------

Most of the code is in src/verifast.ml. See the top of that file for more
help on how to understand that file.

Obviously, before trying to understand the codebase, you should be familiar
with VeriFast from a user's perspective. Go through the VeriFast Tutorial
(in doc/tutorial) and do the exercises. (Unfortunately, not all features
are documented yet. However, all features are tested in the test suite. You
might want to have a look at all examples in the test suite. See
examples/index.html for a description of each test case.
You can most easily browse through the examples at
http://www.cs.kuleuven.be/~bartj/verifast/examples/)
For Java features, see the Java Card tutorial in doc/javacard-tutorial.

You should also be familiar with the symbolic execution approach and
understand why it is sound. A formalization of the core of the approach is
in the "Course notes" TR which you can find on the website. Frederic is
working on an improved and more readable formalization.

Also see the NFM 2011 invited paper on the website for details on
fractional permissions, autosplitting, automerging, and precise predicates.
