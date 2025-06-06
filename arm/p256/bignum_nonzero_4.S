// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// 256-bit nonzeroness test, returning 1 if x is nonzero, 0 if x is zero
// Input x[4]; output function return
//
//    extern uint64_t bignum_nonzero_4(const uint64_t x[static 4]);
//
// Standard ARM ABI: X0 = x, returns X0
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_nonzero_4)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_nonzero_4)
        .text
        .balign 4

#define x x0
#define a x1
#define d x2
#define c x3


S2N_BN_SYMBOL(bignum_nonzero_4):

// Generate a = an OR of all the words in the bignum

        ldp     a, d, [x]
        orr     a, a, d
        ldp     c, d, [x, #16]
        orr     c, c, d
        orr     a, a, c

// Set a standard C condition based on whether a is nonzero

        cmp     a, xzr
        cset    x0, ne

        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
