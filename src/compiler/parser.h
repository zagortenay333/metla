#pragma once

#include "compiler/ast.h"

istruct (Parser);
istruct (Interns);

Parser            *par_new               (Interns *, Mem *);
AstFile           *par_parse_file        (Parser *, IString *filepath);
IString           *par_parse_import_path (Parser *, String path);
AstCodeGen        *par_parse_codegen     (Parser *, String, Ast *, AstFile *, AstLevel);
Void               par_parse_macro_args  (Parser *, AstFile *, ArrayAst *def_args, AstCallMacro *);
AstFile           *par_get_codegen_file  (Parser *);
ArrayAstAttribute *par_get_attributes    (Parser *, AstId);
