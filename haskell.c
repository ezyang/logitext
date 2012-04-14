#include "urweb/urweb.h"
#include "HsFFI.h"
#include "ClassicalFOLFFI_stub.h"
#include <stdio.h>
// actually string option
uw_Basis_string uw_Haskell_refine(uw_context ctx, uw_Basis_string i) {
    uw_Basis_string r = refineFFI(ctx, i);
    return r;
}

uw_Basis_unit uw_Haskell_init(uw_context ctx) {
    hs_init(NULL, NULL);
    ensureIOManagerIsRunning();
}
