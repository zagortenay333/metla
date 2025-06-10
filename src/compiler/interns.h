#pragma once

#include "base/mem.h"
#include "base/map.h"
#include "base/string.h"
#include "compiler/lexer.h"
#include "compiler/sem.h"

istruct (Interns) {
    Mem *mem;
    Map(String, IString*) map;

    IString *asterisk;
    IString *entry_fn_name;

    #define X(_, K) IString *K;
        EACH_KEYWORD(X)
    #undef X

    #define X(N) IString *attr_##N;
        EACH_ATTRIBUTE(X)
    #undef X

    #define X(N) IString *builtin_##N;
        EACH_BUILTIN(X)
    #undef X

    #define X(N, ...) IString *type_##N;
        EACH_SPECIAL_TYPE(X)
    #undef X

    String file_extension;
    String main_file_path;
    String stdlib_file_path;
    String codegen_file_path;
    String file_path_lib_spec;
};

Interns *intern_new  (Mem *mem, String main_file_path);
IString *intern_str  (Interns *, String);
IString *intern_cstr (Interns *, CString);
