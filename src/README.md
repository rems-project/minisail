# minisail

This is a wrapper around the Sail parser and type checker, and the code exported from
Isabelle for the Sail declarative type checker and Sail to MiniSail converter.
Its structure is based on isla/isla-sail.

## Install

This uses the Sail library, which to build and install you will need the latest `sail2` from Github (not the opam
release), and then in the Sail directory run:
```
make isail
make install_libsail
```

Then in this directory do:
```
make
```

## Usage

'''
minisail
  -dump_raw_ast <filename> - Dump type checked Sail AST to specificed file
  -ms_validate - From type checked Sail AST, validate that the AST confirms to declarative specification
  -ms_convert <filename> - From type checked Sail AST, convert to MiniSail and output to specified file.
  <sail file1> ... <sail filen>
'''

