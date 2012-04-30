#include "urweb/urweb.h"
#include "HsFFI.h"
#include "ClassicalFOLFFI_stub.h"
#include <stdio.h>
// actually string option
uw_Basis_string uw_Haskell_refine(uw_context ctx, uw_Basis_string i) {
    return refineFFI(ctx, i);
}

uw_Basis_string uw_Haskell_start(uw_context ctx, uw_Basis_string i) {
    return startFFI(ctx, i);
}

uw_Basis_unit uw_Haskell_init(uw_context ctx) {
    hs_init(NULL, NULL);
    // XXX big ugly hack.  If you remove it the event manager crashes
    // for some odd reason
    ensureIOManagerIsRunning();
    initFFI();
}
