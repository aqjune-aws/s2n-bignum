#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_add_9words)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_add_9words)
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_sub_9words)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_sub_9words)
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_optadd_8words)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_optadd_8words)
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_optadd_9words)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_optadd_9words)
        .text
        .balign 4

S2N_BN_SYMBOL(bignum_add_9words):
        ldp x3, x4, [x1]
        ldp x5, x6, [x2]
        adds x3, x3, x5
        adcs x4, x4, x6
        stp x3, x4, [x0]

        ldp x3, x4, [x1, #16]
        ldp x5, x6, [x2, #16]
        adcs x3, x3, x5
        adcs x4, x4, x6
        stp x3, x4, [x0, #16]

        ldp x3, x4, [x1, #32]
        ldp x5, x6, [x2, #32]
        adcs x3, x3, x5
        adcs x4, x4, x6
        stp x3, x4, [x0, #32]

        ldp x3, x4, [x1, #48]
        ldp x5, x6, [x2, #48]
        adcs x3, x3, x5
        adcs x4, x4, x6
        stp x3, x4, [x0, #48]

        ldr x3, [x1, #64]
        ldr x5, [x2, #64]
        adc x3, x3, x5
        str x3, [x0, #64]

        ret


S2N_BN_SYMBOL(bignum_sub_9words):
        ldp x3, x4, [x1]
        ldp x5, x6, [x2]
        subs x3, x3, x5
        sbcs x4, x4, x6
        stp x3, x4, [x0]

        ldp x3, x4, [x1, #16]
        ldp x5, x6, [x2, #16]
        sbcs x3, x3, x5
        sbcs x4, x4, x6
        stp x3, x4, [x0, #16]

        ldp x3, x4, [x1, #32]
        ldp x5, x6, [x2, #32]
        sbcs x3, x3, x5
        sbcs x4, x4, x6
        stp x3, x4, [x0, #32]

        ldp x3, x4, [x1, #48]
        ldp x5, x6, [x2, #48]
        sbcs x3, x3, x5
        sbcs x4, x4, x6
        stp x3, x4, [x0, #48]

        ldr x3, [x1, #64]
        ldr x5, [x2, #64]
        sbcs x3, x3, x5
        str x3, [x0, #64]

        cset x0, cc
        ret


// z, x, cond, y
S2N_BN_SYMBOL(bignum_optadd_9words):
        cmp x2, xzr
        csetm x2, ne

        ldp x4, x5, [x1]
        ldp x6, x7, [x3]
        and x6, x6, x2
        and x7, x7, x2
        adds x4, x4, x6
        adcs x5, x5, x7
        stp x4, x5, [x0]

        ldp x4, x5, [x1, #16]
        ldp x6, x7, [x3, #16]
        and x6, x6, x2
        and x7, x7, x2
        adcs x4, x4, x6
        adcs x5, x5, x7
        stp x4, x5, [x0, #16]

        ldp x4, x5, [x1, #32]
        ldp x6, x7, [x3, #32]
        and x6, x6, x2
        and x7, x7, x2
        adcs x4, x4, x6
        adcs x5, x5, x7
        stp x4, x5, [x0, #32]

        ldp x4, x5, [x1, #48]
        ldp x6, x7, [x3, #48]
        and x6, x6, x2
        and x7, x7, x2
        adcs x4, x4, x6
        adcs x5, x5, x7
        stp x4, x5, [x0, #48]

        ldr x4, [x1, #64]
        ldr x6, [x3, #64]
        and x6, x6, x2
        adcs x4, x4, x6
        str x4, [x0, #64]

        cset x0, cc
        ret

S2N_BN_SYMBOL(bignum_optadd_8words):
        cmp x2, xzr
        csetm x2, ne

        ldp x4, x5, [x1]
        ldp x6, x7, [x3]
        and x6, x6, x2
        and x7, x7, x2
        adds x4, x4, x6
        adcs x5, x5, x7
        stp x4, x5, [x0]

        ldp x4, x5, [x1, #16]
        ldp x6, x7, [x3, #16]
        and x6, x6, x2
        and x7, x7, x2
        adcs x4, x4, x6
        adcs x5, x5, x7
        stp x4, x5, [x0, #16]

        ldp x4, x5, [x1, #32]
        ldp x6, x7, [x3, #32]
        and x6, x6, x2
        and x7, x7, x2
        adcs x4, x4, x6
        adcs x5, x5, x7
        stp x4, x5, [x0, #32]

        ldp x4, x5, [x1, #48]
        ldp x6, x7, [x3, #48]
        and x6, x6, x2
        and x7, x7, x2
        adcs x4, x4, x6
        adcs x5, x5, x7
        stp x4, x5, [x0, #48]

        adc x0, xzr, xzr
        ret
