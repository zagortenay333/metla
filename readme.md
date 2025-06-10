A toy compiler project for done for studying compilers.

It compiles a custom C-like language to x64 machine code.

It's not in a complete state, in particular there are a
bunch of bugs and the x64 backend doesn't support floats.

The lexer, parser, and semantic analyzer are in a pretty
solid state.

The file `src/compiler/test/test.metla` contains example code.
