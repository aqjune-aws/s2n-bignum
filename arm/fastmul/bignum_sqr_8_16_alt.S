// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Square, z := x^2
// Input x[8]; output z[16]
//
//    extern void bignum_sqr_8_16_alt(uint64_t z[static 16],
//                                    const uint64_t x[static 8]);
//
// Standard ARM ABI: X0 = z, X1 = x
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_sqr_8_16_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_sqr_8_16_alt)
        .text
        .balign 4

#define z x0
#define x x1

#define a0 x2
#define a1 x3
#define a2 x4
#define a3 x5
#define a4 x6
#define a5 x7
#define a6 x8
#define a7 x9

#define l x10

#define u0 x2 // The same as a0, which is safe
#define u1 x11
#define u2 x12
#define u3 x13
#define u4 x14
#define u5 x15
#define u6 x16
#define u7 x17
#define u8 x19
#define u9 x20
#define u10 x21
#define u11 x22
#define u12 x23
#define u13 x24
#define u14 x25
#define u15 x26

S2N_BN_SYMBOL(bignum_sqr_8_16_alt):

// It's convenient to have more registers to play with

        stp     x19, x20, [sp, #-16]!
        stp     x21, x22, [sp, #-16]!
        stp     x23, x24, [sp, #-16]!
        stp     x25, x26, [sp, #-16]!

// Load all the elements as [a7;a6;a5;a4;a3;a2;a1;a0], set up an initial
// window [u8;u7;u6;u5;u4;u3;u2;u1] =  10 + 20 + 30 + 40 + 50 + 60 + 70

        ldp     a0, a1, [x]

        mul     u1, a0, a1
        umulh   u2, a0, a1

        ldp     a2, a3, [x, #16]

        mul     l, a0, a2
        umulh   u3, a0, a2
        adds    u2, u2, l

        ldp     a4, a5, [x, #32]

        mul     l, a0, a3
        umulh   u4, a0, a3
        adcs    u3, u3, l

        ldp     a6, a7, [x, #48]

        mul     l, a0, a4
        umulh   u5, a0, a4
        adcs    u4, u4, l

        mul     l, a0, a5
        umulh   u6, a0, a5
        adcs    u5, u5, l

        mul     l, a0, a6
        umulh   u7, a0, a6
        adcs    u6, u6, l

        mul     l, a0, a7
        umulh   u8, a0, a7
        adcs    u7, u7, l

        adc     u8, u8, xzr

// Add in the next diagonal = 21 + 31 + 41 + 51 + 61 + 71 + 54

        mul     l, a1, a2
        adds    u3, u3, l
        mul     l, a1, a3
        adcs    u4, u4, l
        mul     l, a1, a4
        adcs    u5, u5, l
        mul     l, a1, a5
        adcs    u6, u6, l
        mul     l, a1, a6
        adcs    u7, u7, l
        mul     l, a1, a7
        adcs    u8, u8, l
        cset    u9, cs

        umulh   l, a1, a2
        adds    u4, u4, l
        umulh   l, a1, a3
        adcs    u5, u5, l
        umulh   l, a1, a4
        adcs    u6, u6, l
        umulh   l, a1, a5
        adcs    u7, u7, l
        umulh   l, a1, a6
        adcs    u8, u8, l
        umulh   l, a1, a7
        adc     u9, u9, l
        mul     l, a4, a5
        umulh   u10, a4, a5
        adds    u9, u9, l
        adc     u10, u10, xzr

// And the next one = 32 + 42 + 52 + 62 + 72 + 64 + 65

        mul     l, a2, a3
        adds    u5, u5, l
        mul     l, a2, a4
        adcs    u6, u6, l
        mul     l, a2, a5
        adcs    u7, u7, l
        mul     l, a2, a6
        adcs    u8, u8, l
        mul     l, a2, a7
        adcs    u9, u9, l
        mul     l, a4, a6
        adcs    u10, u10, l
        cset    u11, cs

        umulh   l, a2, a3
        adds    u6, u6, l
        umulh   l, a2, a4
        adcs    u7, u7, l
        umulh   l, a2, a5
        adcs    u8, u8, l
        umulh   l, a2, a6
        adcs    u9, u9, l
        umulh   l, a2, a7
        adcs    u10, u10, l
        umulh   l, a4, a6
        adc     u11, u11, l
        mul     l, a5, a6
        umulh   u12, a5, a6
        adds    u11, u11, l
        adc     u12, u12, xzr

// And the final one = 43 + 53 + 63 + 73 + 74 + 75 + 76

        mul     l, a3, a4
        adds    u7, u7, l
        mul     l, a3, a5
        adcs    u8, u8, l
        mul     l, a3, a6
        adcs    u9, u9, l
        mul     l, a3, a7
        adcs    u10, u10, l
        mul     l, a4, a7
        adcs    u11, u11, l
        mul     l, a5, a7
        adcs    u12, u12, l
        cset    u13, cs

        umulh   l, a3, a4
        adds    u8, u8, l
        umulh   l, a3, a5
        adcs    u9, u9, l
        umulh   l, a3, a6
        adcs    u10, u10, l
        umulh   l, a3, a7
        adcs    u11, u11, l
        umulh   l, a4, a7
        adcs    u12, u12, l
        umulh   l, a5, a7
        adc     u13, u13, l
        mul     l, a6, a7
        umulh   u14, a6, a7
        adds    u13, u13, l
        adc     u14, u14, xzr

// Double that, with u15 holding the top carry

        adds    u1, u1, u1
        adcs    u2, u2, u2
        adcs    u3, u3, u3
        adcs    u4, u4, u4
        adcs    u5, u5, u5
        adcs    u6, u6, u6
        adcs    u7, u7, u7
        adcs    u8, u8, u8
        adcs    u9, u9, u9
        adcs    u10, u10, u10
        adcs    u11, u11, u11
        adcs    u12, u12, u12
        adcs    u13, u13, u13
        adcs    u14, u14, u14
        cset    u15, cs

// Add the homogeneous terms 00 + 11 + 22 + 33 + 44 + 55 + 66 + 77

        umulh   l, a0, a0
        mul     u0, a0, a0
        adds    u1, u1, l

        mul     l, a1, a1
        adcs    u2, u2, l
        umulh   l, a1, a1
        adcs    u3, u3, l

        mul     l, a2, a2
        adcs    u4, u4, l
        umulh   l, a2, a2
        adcs    u5, u5, l

        mul     l, a3, a3
        adcs    u6, u6, l
        umulh   l, a3, a3
        adcs    u7, u7, l

        mul     l, a4, a4
        adcs    u8, u8, l
        umulh   l, a4, a4
        adcs    u9, u9, l

        mul     l, a5, a5
        adcs    u10, u10, l
        umulh   l, a5, a5
        adcs    u11, u11, l

        mul     l, a6, a6
        adcs    u12, u12, l
        umulh   l, a6, a6
        adcs    u13, u13, l

        mul     l, a7, a7
        adcs    u14, u14, l
        umulh   l, a7, a7
        adc     u15, u15, l

// Store back final result

        stp     u0, u1, [z]
        stp     u2, u3, [z, #16]
        stp     u4, u5, [z, #32]
        stp     u6, u7, [z, #48]
        stp     u8, u9, [z, #64]
        stp     u10, u11, [z, #80]
        stp     u12, u13, [z, #96]
        stp     u14, u15, [z, #112]

// Restore registers and return

        ldp     x25, x26, [sp], #16
        ldp     x23, x24, [sp], #16
        ldp     x21, x22, [sp], #16
        ldp     x19, x20, [sp], #16

        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
