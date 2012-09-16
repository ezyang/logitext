#include "urweb/urweb.h"
#include "HsFFI.h"
#include "ClassicalFOLFFI_stub.h"
#include "LinearFFI_stub.h"
#include "CommonFFI_stub.h"
#include "IntuitionisticFFI_stub.h"
#include <stdio.h>

void initGHC() {
    int my_argc = 1;
    char *my_argv[] = { "<logitext>", NULL };
    char **my_argv2 = (char**)my_argv; // silly types...
    hs_init(&my_argc, &my_argv2);
    // XXX big ugly hack.  If you remove it the event manager crashes
    // for some odd reason
    ensureIOManagerIsRunning();
}

// dup dup
uw_Basis_unit uw_Haskell_initClassicalFOL(uw_context ctx) {
    initGHC();
    _uw_Haskell_initClassicalFOL();
}

uw_Basis_unit uw_Haskell_initVanilla(uw_context ctx) {
    initGHC();
}
