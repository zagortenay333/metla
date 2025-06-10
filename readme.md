A toy compiler project done for the purpose of studying compilers.

It compiles a custom C-like language to x64 machine code.

The file `src/compiler/test/test.metla` contains example code.

The compiler architecture has 3 parts:

  1. A pretty solid frontend: lexer, parser, semantic analyzer.
  2. An SSA based IR called Sir that includes some optimizations
     like sparse conditional constants propagation, as well as
     a register allocator from the linear-scan family.
  3. An incomplete x64 backend that doesn't support floats.
