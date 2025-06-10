A toy compiler project done for the purpose of studying compilers.

It compiles a custom C-like language to x64 machine code.

The file `src/compiler/test/test.metla` contains example code.

The compiler architecture has 3 parts:

  1. A pretty solid frontend: lexer, parser, semantic analyzer.
  2. An SSA based IR called Sir that comes with some optimizations.
  3. A crappy x64 backend that doesn't support floats.
