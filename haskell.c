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

uw_Basis_string uw_Haskell_parseUniverse(uw_context ctx, uw_Basis_string i) {
    return parseUniverseFFI(ctx, i);
}

uw_Basis_unit uw_Haskell_init(uw_context ctx) {
    int my_argc = 1;
    char *my_argv[] = { "<unknown>", NULL };
    char **my_argv2 = (char**)my_argv; // silly types...
    hs_init(&my_argc, &my_argv2);
    // XXX big ugly hack.  If you remove it the event manager crashes
    // for some odd reason
    ensureIOManagerIsRunning();
    initFFI();
}
