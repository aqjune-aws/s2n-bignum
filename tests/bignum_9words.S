#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_add_9words)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_add_9words)
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_add_9words_1word)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_add_9words_1word)
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_sub_9words)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_sub_9words)
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_ge_9words)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_ge_9words)
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_optadd_8words)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_optadd_8words)
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_optadd_9words)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_optadd_9words)
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_optsub_9words)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_optsub_9words)
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_optneg_9words)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_optneg_9words)

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_add_mod_2_to_513_minus1)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_add_mod_2_to_513_minus1)

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

S2N_BN_SYMBOL(bignum_add_9words_1word):
        ldp x3, x4, [x1]
        adds x3, x3, x2
        adcs x4, x4, xzr
        stp x3, x4, [x0]

        ldp x3, x4, [x1, #16]
        adcs x3, x3, xzr
        adcs x4, x4, xzr
        stp x3, x4, [x0, #16]

        ldp x3, x4, [x1, #32]
        adcs x3, x3, xzr
        adcs x4, x4, xzr
        stp x3, x4, [x0, #32]

        ldp x3, x4, [x1, #48]
        adcs x3, x3, xzr
        adcs x4, x4, xzr
        stp x3, x4, [x0, #48]

        ldr x3, [x1, #64]
        adc x3, x3, xzr
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

S2N_BN_SYMBOL(bignum_ge_9words):
        ldp x3, x4, [x0]
        ldp x5, x6, [x1]
        subs xzr, x3, x5
        sbcs xzr, x4, x6

        ldp x3, x4, [x0, #16]
        ldp x5, x6, [x1, #16]
        sbcs xzr, x3, x5
        sbcs xzr, x4, x6

        ldp x3, x4, [x0, #32]
        ldp x5, x6, [x1, #32]
        sbcs xzr, x3, x5
        sbcs xzr, x4, x6

        ldp x3, x4, [x0, #48]
        ldp x5, x6, [x1, #48]
        sbcs xzr, x3, x5
        sbcs xzr, x4, x6

        ldr x3, [x0, #64]
        ldr x5, [x1, #64]
        sbcs xzr, x3, x5

        cset x0, cs
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

// z, x, cond, y
S2N_BN_SYMBOL(bignum_optsub_9words):
        cmp x2, xzr
        csetm x2, ne

        ldp x4, x5, [x1]
        ldp x6, x7, [x3]
        and x6, x6, x2
        and x7, x7, x2
        subs x4, x4, x6
        sbcs x5, x5, x7
        stp x4, x5, [x0]

        ldp x4, x5, [x1, #16]
        ldp x6, x7, [x3, #16]
        and x6, x6, x2
        and x7, x7, x2
        sbcs x4, x4, x6
        sbcs x5, x5, x7
        stp x4, x5, [x0, #16]

        ldp x4, x5, [x1, #32]
        ldp x6, x7, [x3, #32]
        and x6, x6, x2
        and x7, x7, x2
        sbcs x4, x4, x6
        sbcs x5, x5, x7
        stp x4, x5, [x0, #32]

        ldp x4, x5, [x1, #48]
        ldp x6, x7, [x3, #48]
        and x6, x6, x2
        and x7, x7, x2
        sbcs x4, x4, x6
        sbcs x5, x5, x7
        stp x4, x5, [x0, #48]

        ldr x4, [x1, #64]
        ldr x6, [x3, #64]
        and x6, x6, x2
        sbc x4, x4, x6
        str x4, [x0, #64]

        ret

// z, x, cond, y
S2N_BN_SYMBOL(bignum_optneg_9words):
        cmp x1, xzr
        csetm x1, ne

        adds xzr, x1, x1

        ldp x4, x5, [x2]
        eor x4, x4, x1
        adcs x4, x4, xzr
        eor x5, x5, x1
        adcs x5, x5, xzr
        stp x4, x5, [x0]

        ldp x4, x5, [x2, #16]
        eor x4, x4, x1
        adcs x4, x4, xzr
        eor x5, x5, x1
        adcs x5, x5, xzr
        stp x4, x5, [x0, #16]

        ldp x4, x5, [x2, #32]
        eor x4, x4, x1
        adcs x4, x4, xzr
        eor x5, x5, x1
        adcs x5, x5, xzr
        stp x4, x5, [x0, #32]

        ldp x4, x5, [x2, #48]
        eor x4, x4, x1
        adcs x4, x4, xzr
        eor x5, x5, x1
        adcs x5, x5, xzr
        stp x4, x5, [x0, #48]

        ldr x4, [x2, #64]
        eor x4, x4, x1
        adcs x4, x4, xzr
        str x4, [x0, #64]

        ret

// can be <= 2_to_513_minus1
S2N_BN_SYMBOL(bignum_add_mod_2_to_513_minus1):
        // x1[0..8] + x2[0..8]
        // x0[0..8]: output
        ldp x3, x4, [x1]
        ldp x14, x15, [x2]
        adds x3, x3, x14
        adcs x4, x4, x15

        ldp x5, x6, [x1,#16]
        ldp x14, x15, [x2,#16]
        adcs x5, x5, x14
        adcs x6, x6, x15

        ldp x7, x8, [x1,#32]
        ldp x14, x15, [x2,#32]
        adcs x7, x7, x14
        adcs x8, x8, x15

        ldp x9, x10, [x1,#48]
        ldp x14, x15, [x2,#48]
        adcs x9, x9, x14
        adcs x10, x10, x15

        ldr x11, [x1,#64]
        ldr x14, [x2,#64]
        adc x11, x11, x14
        lsr x12, x11, 1
        and x11, x11, 1

        adds x3, x3, x12
        adcs x4, x4, xzr
        adcs x5, x5, xzr
        adcs x6, x6, xzr
        adcs x7, x7, xzr
        adcs x8, x8, xzr
        adcs x9, x9, xzr
        adcs x10, x10, xzr
        adc x11, x11, xzr
        stp x3, x4, [x0]
        stp x5, x6, [x0, #16]
        stp x7, x8, [x0, #32]
        stp x9, x10, [x0, #48]
        str x11, [x0, #64]

        ret
