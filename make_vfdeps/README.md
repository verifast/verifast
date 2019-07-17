Building the VFDeps package
===========================

For macOS
---------

0. Install the dependencies, as described in [`README.MacOS.md`](../README.MacOS.md), except for the OCaml-based ones (which we will be building below).
1. If you have an Opam install in `~/.opam`, hide it (by renaming it). (Otherwise, `ocamlbuild` will install its binaries there instead of in the specified `PREFIX`.)
2. Run `export PKG_CONFIG_PATH=/usr/local/opt/libffi/lib/pkgconfig`
3. Create the target directory `/usr/local/vfdeps-YY.MM`
  1. Run `sudo mkdir /usr/local/vfdeps-YY.MM`
  2. Run `sudo chown ME /usr/local/vfdeps-YY.MM`
4. Run `make -f Makefile.deps PREFIX=/usr/local/vfdeps-YY.MM`
5. Run `cd /usr/local; tar cjf ~/vfdeps-YY.MM-macos.txz vfdeps-YY.MM`
