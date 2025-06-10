#pragma once

#include "base/mem.h"
#include "compiler/sir.h"

Void sir_optimize                  (SirFn *, Mem *);
Void sir_simplify_cfg              (SirFn *);
Void sir_remove_unused_items       (SirFn *);
Void sir_remove_unreachable_blocks (SirFn *);
Void sir_mark_reachable_blocks     (SirFn *, SirBlock *);
