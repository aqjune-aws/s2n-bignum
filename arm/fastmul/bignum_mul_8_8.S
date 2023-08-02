// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// ----------------------------------------------------------------------------
// Multiply z := x * y
// Inputs x[8], y[8]; output z[8]
//
//    extern void bignum_mul_8_8
//     (uint64_t z[static 8], uint64_t x[static 8], uint64_t y[static 8]);
//
// Standard ARM ABI: X0 = z, X1 = x, X2 = y
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_mul_8_8)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_mul_8_8)
        .text
        .balign 4

// ---------------------------------------------------------------------------
// Macro computing [c,b,a] := [b,a] + (x - y) * (w - z), adding with carry
// to the [b,a] components but leaving CF aligned with the c term, which is
// a sign bitmask for (x - y) * (w - z). Continued add-with-carry operations
// with [c,...,c] will continue the carry chain correctly starting from
// the c position if desired to add to a longer term of the form [...,b,a].
//
// c,h,l,t should all be different and t,h should not overlap w,z.
// ---------------------------------------------------------------------------

.macro muldiffnadd b,a, c,h,l,t, x,y, w,z
        subs    \t, \x, \y
        cneg    \t, \t, cc
        csetm   \c, cc
        subs    \h, \w, \z
        cneg    \h, \h, cc
        mul     \l, \t, \h
        umulh   \h, \t, \h
        cinv    \c, \c, cc
        adds    xzr, \c, #1
        eor     \l, \l, \c
        adcs    \a, \a, \l
        eor     \h, \h, \c
        adcs    \b, \b, \h
.endm

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

// These alias the ax and bx values, and are only used when they are done with

#define u0  x3
#define u1  x4
#define u2  x5
#define u3  x6
#define u4  x7
#define u5  x8
#define u6  x9
#define u7  x10

// These alias c,h,l,m but leave s, t and d safe, all we need

#define u8  x20
#define u9  x21
#define u10 x22
#define u11 x23

// We recycle the input pointers near the end

#define s  x1
#define d  x2

// ---------------------------------------------------------------------------
// Core 4x4->8 ADK multiplication macro
// Does [s7,s6,s5,s4,s3,s2,s1,s0] = [a3,a2,a1,a0] * [b3,b2,b1,b0]
//
// If the input parameter is 1, it also adds in [z+32,z+40,z+48,z+56]
// existing contents; if the parameter is 0 it just does the pure multiply
// ---------------------------------------------------------------------------

.macro  mul4 afl

// First accumulate all the "simple" products as [s7,s6,s5,s4,s0]

        mul     s0, a0, b0
        mul     s4, a1, b1
        mul     s5, a2, b2
        mul     s6, a3, b3

        umulh   s7, a0, b0
        adds    s4, s4, s7
        umulh   s7, a1, b1
        adcs    s5, s5, s7
        umulh   s7, a2, b2
        adcs    s6, s6, s7
        umulh   s7, a3, b3
        adc     s7, s7, xzr

// Multiply by B + 1 to get [s7;s6;s5;s4;s1;s0]

        adds    s1, s4, s0
        adcs    s4, s5, s4
        adcs    s5, s6, s5
        adcs    s6, s7, s6
        adc     s7, xzr, s7

// Multiply by B^2 + 1 to get [s7;s6;s5;s4;s3;s2;s1;s0]

        adds    s2, s4, s0
        adcs    s3, s5, s1
        adcs    s4, s6, s4
        adcs    s5, s7, s5
        adcs    s6, xzr, s6
        adc     s7, xzr, s7

// Optionally add the existing z contents

.rep \afl
        ldp     l, h, [z,#32]
        adds    s0, s0, l
        adcs    s1, s1, h
        ldp     l, h, [z,#48]
        adcs    s2, s2, l
        adcs    s3, s3, h
        adcs    s4, s4, xzr
        adcs    s5, s5, xzr
        adcs    s6, s6, xzr
        adc     s7, s7, xzr
.endr

// Now add in all the "complicated" terms.

        muldiffnadd s6,s5, c,h,l,t, a2,a3, b3,b2
        adc     s7, s7, c

        muldiffnadd s2,s1, c,h,l,t, a0,a1, b1,b0
        adcs    s3, s3, c
        adcs    s4, s4, c
        adcs    s5, s5, c
        adcs    s6, s6, c
        adc     s7, s7, c

        muldiffnadd s5,s4, c,h,l,t, a1,a3, b3,b1
        adcs    s6, s6, c
        adc     s7, s7, c

        muldiffnadd s3,s2, c,h,l,t, a0,a2, b2,b0
        adcs    s4, s4, c
        adcs    s5, s5, c
        adcs    s6, s6, c
        adc     s7, s7, c

        muldiffnadd s4,s3, c,h,l,t, a0,a3, b3,b0
        adcs    s5, s5, c
        adcs    s6, s6, c
        adc     s7, s7, c
        muldiffnadd s4,s3, c,h,l,t, a1,a2, b2,b1
        adcs    s5, s5, c
        adcs    s6, s6, c
        adc     s7, s7, c
.endm

// ---------------------------------------------------------------------------
// The main code
// ---------------------------------------------------------------------------

S2N_BN_SYMBOL(bignum_mul_8_8):

// Save registers

        stp     x19, x20, [sp, #-16]!
        stp     x21, x22, [sp, #-16]!
        stp     x23, x24, [sp, #-16]!

// Multiply the low halves and then the high halves using ADK 4x4->8.
// For the second one add the top of the low part (Q1) already into
// the bottom of the high part (Q2) so that is already dealt with.
//
// Write back the first one but defer the second till a bit later while
// we get on with the absolute difference computations

        ldp     a0, a1, [x]
        ldp     b0, b1, [y]
        ldp     a2, a3, [x, #16]
        ldp     b2, b3, [y, #16]

        mul4    0

        stp     s0, s1, [z]
        stp     s2, s3, [z, #16]
        stp     s4, s5, [z, #32]
        stp     s6, s7, [z, #48]


        ldp     a0, a1, [x, #32]
        ldp     a2, a3, [x, #48]
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

        ldp   s4, s5, [z, #32]
        adds  s4, s4, s0
        adcs  s5, s5, s1
        stp   s4, s5, [z, #32]
        ldp   s6, s7, [z, #48]
        adcs  s6, s6, s2
        adc   s7, s7, s3
        stp   s6, s7, [z, #48]


        ldp     a0, a1, [x]
        ldp     a2, a3, [x, #16]
        ldp     b0, b1, [y, #32]
        ldp     b2, b3, [y, #48]

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

        ldp   s4, s5, [z, #32]
        adds  s4, s4, s0
        adcs  s5, s5, s1
        stp   s4, s5, [z, #32]
        ldp   s6, s7, [z, #48]
        adcs  s6, s6, s2
        adc   s7, s7, s3
        stp   s6, s7, [z, #48]

// Restore regs and return

        ldp     x23, x24, [sp], #16
        ldp     x21, x22, [sp], #16
        ldp     x19, x20, [sp], #16

        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
