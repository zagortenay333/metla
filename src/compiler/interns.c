#include "base/map.h"
#include "base/string.h"
#include "compiler/interns.h"

IString *intern_str (Interns *interns, String str) {
    IString *intern = map_get_ptr(&interns->map, str);

    if (! intern) {
        intern  = mem_new(interns->mem, IString);
        *intern = str;
        map_add(&interns->map, str, intern);
    }

    return intern;
}

IString *intern_cstr (Interns *interns, CString cstr) {
    return intern_str(interns, str(cstr));
}

Interns *intern_new (Mem *mem, String main_file_path) {
    Interns *interns = mem_new(mem, Interns);

    interns->mem                = mem;
    interns->main_file_path     = main_file_path,
    interns->file_extension     = str(".metla");
    interns->file_path_lib_spec = str("%stdlib");
    interns->stdlib_file_path   = str("/home/zagor/code/metla/src/compiler/stdlib");
    interns->codegen_file_path  = str("/home/zagor/code/metla/.codegen.edili");

    map_init(&interns->map, mem);

    interns->asterisk = intern_cstr(interns, "*");
    interns->entry_fn_name = intern_cstr(interns, "main");

    #define X(key, KEY) interns->KEY = intern_cstr(interns, #key);
        EACH_KEYWORD(X)
    #undef X

    #define X(N) interns->attr_##N = intern_cstr(interns, #N);
        EACH_ATTRIBUTE(X)
    #undef X

    #define X(N) interns->builtin_##N = intern_cstr(interns, #N);
        EACH_BUILTIN(X)
    #undef X

    #define X(N, T) interns->type_##N = intern_cstr(interns, #T);
        EACH_SPECIAL_TYPE(X)
    #undef X

    return interns;
}
