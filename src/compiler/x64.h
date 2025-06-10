#pragma once

// =============================================================================
// Overview:
// ---------
//
// This main purpose of this module is to:
//
//     1. Generate Sir for a typechecked program.
//     2. Perform x64 specific actions on Sir.
//     3. Emit executable.
//
// @abi Hardcoded assumptions about the abi:
// -----------------------------------------
//
// At the moment we only have 1 compiler target (Linux x64), so we
// take the liberty to hardcode some things into this module that
// should be separated into other modules once we have more targets.
//
//     1. We only have 1 calling convention at the moment which is
//        our own internal one. This assumption is hardcoded in the
//        way the init_reg_constraints() function is written.
//
//     2. We emit a Linux specific ELF file. For example the start
//        function follows the sysV spec.
//
// =============================================================================
#include "compiler/sir.h"
#include "compiler/abi.h"
#include "compiler/sem.h"
#include "compiler/interns.h"

Void x64_emit    (String exe_file_path, Mem *, Abi *, Interns *, Sem *, SemProgram);
Abi *x64_abi_new (Mem *, Sem *);
Void x64_test    (String main_file_path);
