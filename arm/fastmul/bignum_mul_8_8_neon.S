// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// ----------------------------------------------------------------------------
// Multiply z := x * y
// Inputs x[8], y[8]; output z[8]
//
//    extern void bignum_mul_8_8_neon
//     (uint64_t z[static 8], uint64_t x[static 8], uint64_t y[static 8]);
//
// Standard ARM ABI: X0 = z, X1 = x, X2 = y
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_mul_8_8_neon)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_mul_8_8_neon)
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
#define t  x23

#define u0 x24
#define u1 x25
#define u2 x26
#define u3 x27
#define u4 x28
#define u5 x29
#define u6 x30

// ---------------------------------------------------------------------------
// The main code
// ---------------------------------------------------------------------------

S2N_BN_SYMBOL(bignum_mul_8_8_neon):

        // Save registers

        stp     x19, x20, [sp, #-16]!
        stp     x21, x22, [sp, #-16]!
        stp     x23, x24, [sp, #-16]!
        stp     x25, x26, [sp, #-16]!
        stp     x27, x28, [sp, #-16]!
        stp     x29, x30, [sp, #-16]!


        //////// Does [s7,s6,s5,s4,s3,s2,s1,s0] = [a3,a2,a1,a0] * [b3,b2,b1,b0]
        // Multiply the low halves and then the high halves using ADK 4x4->8.
        // For the second one add the top of the low part (Q1) already into
        // the bottom of the high part (Q2) so that is already dealt with.
        //
        // Write back the first one but defer the second till a bit later while
        // we get on with the absolute difference computations

// NEON: Calculate (x[16] * y[16], x[24] * y[24]) (= (a2*b2, a3*b3))
movi    v19.2d, #0x000000ffffffff

ldr     q21, [x, #16]
ldr     q22, [y, #16]
#define in1  v21
#define in2  v22
#define out_lo v0
#define out_hi v1
uzp2    v3.4s, in2.4s, in1.4s
xtn     v4.2s, in1.2d
xtn     v5.2s, in2.2d
rev64   v1.4s, in2.4s

        ldp     a0, a1, [x]
        ldp     b0, b1, [y]

umull   v6.2d, v4.2s, v5.2s
umull   v7.2d, v4.2s, v3.2s
uzp2    v16.4s, in1.4s, in1.4s
mul     v0.4s, v1.4s, in1.4s

        ldp     a2, a3, [x, #16]
        ldp     b2, b3, [y, #16]

usra    v7.2d, v6.2d, #32
umull   out_hi.2d, v16.2s, v3.2s
uaddlp  v0.2d, v0.4s
and     v2.16b, v7.16b, v19.16b

        // First accumulate all the "simple" products as [s7,s6,s5,s4,s0]

        mul     s0, a0, b0
        mul     s4, a1, b1

umlal   v2.2d, v16.2s, v5.2s
shl     out_lo.2d, v0.2d, #32
usra    out_hi.2d, v7.2d, #32
umlal   out_lo.2d, v4.2s, v5.2s

        umulh   s7, a0, b0

mov u0, out_lo.d[0] // low(x[16] * y[16])
mov u1, out_lo.d[1] // low(x[24] * y[24])
usra    out_hi.2d, v2.2d, #32

        umulh   t, a1, b1

mov u2, out_hi.d[0] // high(x[16] * y[16])
mov u3, out_hi.d[1] // high(x[24] * y[24])
#undef in1
#undef in2
#undef out_lo
#undef out_hi

// NEON: Calculate (x[32]*y[0], x[40]*y[0]) as well as (x[48]*y[0], x[56]*y[0])
//       for next 8x8->8 words multiplication (x_hi * y_lo)
#define in1  v20
dup v20.2d, b0
xtn     v4.2s, in1.2d
uzp2    v16.4s, in1.4s, in1.4s

        adds    s4, s4, s7
        adcs    s5, u0, t

// NEON: calculate (x[32]*y[0], x[40]*y[0])
// The result is stord in out_lo and out_hi as follows:
//    out_hi = high 64 bits of (x[32]*y[0], x[40]*y[0])
//    out_lo = low 64 bits of  (x[32]*y[0], x[40]*y[0])
ldr     q21, [x, #32]
ldr     q22, [x, #48]

#define in2  v21
#define out_lo v0
#define out_hi v1
uzp2    v3.4s, in2.4s, in1.4s
xtn     v5.2s, in2.2d
rev64   v1.4s, in2.4s

        adcs    s6, u1, u2
        adc     s7, u3, xzr

umull   v6.2d, v4.2s, v5.2s
umull   v7.2d, v4.2s, v3.2s
mul     v0.4s, v1.4s, in1.4s

usra    v7.2d, v6.2d, #32
umull   out_hi.2d, v16.2s, v3.2s
uaddlp  v0.2d, v0.4s
and     v2.16b, v7.16b, v19.16b

umlal   v2.2d, v16.2s, v5.2s
shl     out_lo.2d, v0.2d, #32
usra    out_hi.2d, v7.2d, #32
umlal   out_lo.2d, v4.2s, v5.2s

mov u0, out_lo.d[0] // low64(x[32] * y[0])
mov u1, out_lo.d[1] // low64(x[40] * y[0])

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

usra    out_hi.2d, v2.2d, #32
mov u2, out_hi.d[0] // high64(x[32] * y[0])
mov u3, out_hi.d[1] // high64(x[40] * y[0])

#undef in2
#undef out_lo
#undef out_hi

// NEON: calculate (x[48]*y[0], x[56]*y[0])
#define in2  v22
#define out_lo v23
#define out_hi v24
uzp2    v3.4s, in2.4s, in1.4s
xtn     v5.2s, in2.2d
rev64   v1.4s, in2.4s

        // Now add in all the "complicated" terms.

        muldiffnadd s6,s5, c,h,l,t, a2,a3, b3,b2
        adc     s7, s7, c

umull   v6.2d, v4.2s, v5.2s
umull   v7.2d, v4.2s, v3.2s
mul     v0.4s, v1.4s, in1.4s

        muldiffnadd s2,s1, c,h,l,t, a0,a1, b1,b0
        adcs    s3, s3, c
        adcs    s4, s4, c
        adcs    s5, s5, c
        adcs    s6, s6, c
        adc     s7, s7, c

usra    v7.2d, v6.2d, #32
umull   out_hi.2d, v16.2s, v3.2s
uaddlp  v0.2d, v0.4s
and     v2.16b, v7.16b, v19.16b

        muldiffnadd s5,s4, c,h,l,t, a1,a3, b3,b1
        adcs    s6, s6, c
        adc     s7, s7, c

umlal   v2.2d, v16.2s, v5.2s
shl     out_lo.2d, v0.2d, #32
usra    out_hi.2d, v7.2d, #32
umlal   out_lo.2d, v4.2s, v5.2s

        muldiffnadd s3,s2, c,h,l,t, a0,a2, b2,b0
        adcs    s4, s4, c
        adcs    s5, s5, c
        adcs    s6, s6, c
        adc     s7, s7, c

mov u4, out_lo.d[0] // low64(x[48] * y[0])
mov u5, out_lo.d[1] // low64(x[56] * y[0])
usra    out_hi.2d, v2.2d, #32
mov u6, out_hi.d[0] // high64(x[48] * y[0])
#undef in1
#undef in2
#undef out_lo
#undef out_hi

        muldiffnadd s4,s3, c,h,l,t, a0,a3, b3,b0
        adcs    s5, s5, c
        adcs    s6, s6, c
        adc     s7, s7, c

// NEON: Calculate (x[0]*y[32], x[8]*y[32]) as well as
//       (x[16]*y[32], x[24]*y[32]) for next x_lo * y_hi
ldp     h, xzr, [y, #32]
#define in1  v20
dup v20.2d, h
xtn     v4.2s, in1.2d
uzp2    v16.4s, in1.4s, in1.4s

        muldiffnadd s4,s3, c,h,l,t, a1,a2, b2,b1

// NEON: do (x[0]*y[32], x[8]*y[32])
ldr     q21, [x]
ldr     q22, [x, #16]

        adcs    s5, s5, c
        adcs    s6, s6, c
        adc     s7, s7, c

        stp     s0, s1, [z]
        stp     s2, s3, [z, #16]

#define in2  v21
#define out_lo v0
#define out_hi v1
uzp2    v3.4s, in2.4s, in1.4s
xtn     v5.2s, in2.2d
rev64   v1.4s, in2.4s
umull   v6.2d, v4.2s, v5.2s

        //////// x_hi * y_lo

        ldp     a0, a1, [x, #32]
        ldp     a2, a3, [x, #48]
        ldp     b0, b1, [y]
        ldp     b2, b3, [y, #16]

umull   v7.2d, v4.2s, v3.2s
mul     v0.4s, v1.4s, in1.4s
usra    v7.2d, v6.2d, #32
umull   out_hi.2d, v16.2s, v3.2s

        adds  s1, u1, u2
        adcs  s2, u3, u4
        adc   s3, u5, u6

uaddlp  v0.2d, v0.4s
and     v2.16b, v7.16b, v19.16b
umlal   v2.2d, v16.2s, v5.2s
shl     out_lo.2d, v0.2d, #32

        mul   t,  a0, b1
        adds  s1, s1, t
        mul   t,  a1, b1
        adcs  s2, s2, t

usra    out_hi.2d, v7.2d, #32
umlal   out_lo.2d, v4.2s, v5.2s

        mul   t,  a2, b1
        adc   s3, s3, t

mov u1, out_lo.d[1] // low64(x[8] * y[32])
usra    out_hi.2d, v2.2d, #32
mov u2, out_hi.d[0] // high64(x[0] * y[32])

        umulh t, a0, b1
        adds  s2, s2, t

mov u3, out_hi.d[1] // high64(x[8] * y[32])
mov h,  out_lo.d[0] // low64(x[0] * y[32])

#undef in2
#undef out_lo
#undef out_hi

        umulh t, a1, b1
        adc   s3, s3, t
        mul   t, a0, b2
        adds  s2, s2, t

// NEON: do (x[16]*y[32], x[24]*y[32])
#define in2  v22
#define out_lo v23
#define out_hi v24
uzp2    v3.4s, in2.4s, in1.4s
xtn     v5.2s, in2.2d
rev64   v1.4s, in2.4s
umull   v6.2d, v4.2s, v5.2s

        mul   t, a1, b2
        adc   s3, s3, t
        umulh t, a0, b2
        add   s3, s3, t

umull   v7.2d, v4.2s, v3.2s
mul     v0.4s, v1.4s, in1.4s
usra    v7.2d, v6.2d, #32
umull   out_hi.2d, v16.2s, v3.2s

        mul   t, a0, b3
        add   s3, s3, t

        adds  s4, s4, u0

uaddlp  v0.2d, v0.4s
and     v2.16b, v7.16b, v19.16b
umlal   v2.2d, v16.2s, v5.2s
shl     out_lo.2d, v0.2d, #32

mov u0, h // from previous Neon mults.

usra    out_hi.2d, v7.2d, #32
umlal   out_lo.2d, v4.2s, v5.2s
mov u4, out_lo.d[0] // low64(x[16] * y[32])
mov u5, out_lo.d[1] // low64(x[24] * y[32])

        adcs  s5, s5, s1
        adcs  s6, s6, s2
        adc   s7, s7, s3

usra    out_hi.2d, v2.2d, #32
mov u6, out_hi.d[0] // high64(x[16] * y[32])

#undef in2
#undef out_lo
#undef out_hi
#undef in1

// NEON: do (x[0] * y[48], x[8] * y[48]), but 64x64->64 mults only
ldr q21, [x]

        ///////// x_lo * y_hi
        ldp     a0, a1, [x]
        ldp     a2, a3, [x, #16]
        ldp     b0, b1, [y, #32]
        ldp     b2, b3, [y, #48]

dup v20.2d, b2
#define in1 v20
#define in2 v21
uzp1 v2.4s, in2.4s, in1.4s
rev64 v1.4s, in2.4s

        adds  s1, u1, u2
        adcs  s2, u4, u3
        adc   s3, u5, u6

uzp1 v3.4s, in1.4s, in1.4s
mul v0.4s, v1.4s, in1.4s

        mul   t,  a0, b1
        adds  s1, s1, t

uaddlp v0.2d, v0.4s
shl v0.2d, v0.2d, #32

        mul   t,  a1, b1
        adcs  s2, s2, t

umlal v0.2d, v3.2s, v2.2s
mov u2, v0.d[0]
mov u3, v0.d[1]
#undef in1
#undef in2

        mul   t,  a2, b1
        adc   s3, s3, t

        umulh t, a0, b1
        adds  s2, s2, t
        umulh t, a1, b1
        adc   s3, s3, t

        adds  s2, s2, u2
        adc   s3, s3, u3

        umulh t, a0, b2
        add   s3, s3, t

        mul   t, a0, b3
        add   s3, s3, t

        adds  s4, s4, u0
        adcs  s5, s5, s1
        stp   s4, s5, [z, #32]
        adcs  s6, s6, s2
        adc   s7, s7, s3
        stp   s6, s7, [z, #48]

// Restore regs and return

        ldp     x29, x30, [sp], #16
        ldp     x27, x28, [sp], #16
        ldp     x25, x26, [sp], #16
        ldp     x23, x24, [sp], #16
        ldp     x21, x22, [sp], #16
        ldp     x19, x20, [sp], #16

        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
