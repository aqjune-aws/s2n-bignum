// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// ----------------------------------------------------------------------------
// Multiply z := x * y
// Inputs x[4], y[4]; output z[8]
//
//    extern void bignum_mul_4_8
//      (uint64_t z[static 8], uint64_t x[static 4], uint64_t y[static 4]);
//
// Standard ARM ABI: X0 = z, X1 = x, X2 = y
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_mul_4_4)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_mul_4_4)
        .text
        .balign 4

#define z x0
#define x x1
#define y x2

#define a0 x3
#define a1 x4
#define a2 x5
#define a3 x6
#define b0 x7
#define b1 x8
#define b2 x9
#define b3 x10

#define s0 x11
#define s1 x12
#define s2 x13
#define s3 x14
#define s4 x15
#define s5 x16
#define s6 x17
#define s7 x19

#define c  x20
#define h  x21
#define l  x22
#define m  x23
#define t  x24

S2N_BN_SYMBOL(bignum_mul_4_4):


        stp     x19, x20, [sp, #-16]!
        stp     x21, x22, [sp, #-16]!
        stp     x23, x24, [sp, #-16]!


        ldp     a0, a1, [x]
        ldp     a2, a3, [x, #16]
        ldp     b0, b1, [y]
        ldp     b2, b3, [y, #16]

        mul   s0, a0, b0
        mul   s1, a1, b0
        mul   s2, a2, b0
        mul   s3, a3, b0

        umulh t,  a0, b0
        adds  s1, s1, t
        umulh t,  a1, b0
        adcs  s2, s2, t
        umulh t,  a2, b0
        adc   s3, s3, t

        mul   t,  a0, b1
        adds  s1, s1, t
        mul   t,  a1, b1
        adcs  s2, s2, t
        mul   t,  a2, b1
        adc   s3, s3, t

        umulh t, a0, b1
        adds  s2, s2, t
        umulh t, a1, b1
        adc   s3, s3, t

        mul   t, a0, b2
        adds  s2, s2, t
        mul   t, a1, b2
        adc   s3, s3, t

        umulh t, a0, b2
        add   s3, s3, t

        mul   t, a0, b3
        add   s3, s3, t

        stp   s0, s1, [z]
        stp   s2, s3, [z, #16]

        ldp     x23, x24, [sp], #16
        ldp     x21, x22, [sp], #16
        ldp     x19, x20, [sp], #16

        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
