#include "urweb/urweb.h"
#include "HsFFI.h"
#include "ClassicalFOLFFI_stub.h"
uw_Basis_int uw_Haskell_test(uw_context ctx, uw_Basis_int n) {
    foo();
    return n;
}
uw_Basis_unit uw_Haskell_init(uw_context ctx) {
    hs_init(NULL, NULL);
}
