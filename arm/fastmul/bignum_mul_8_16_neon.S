// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// ----------------------------------------------------------------------------
// Multiply z := x * y
// Inputs x[8], y[8]; output z[16]
//
//    extern void bignum_mul_8_16_neon
//     (uint64_t z[static 16], uint64_t x[static 8], uint64_t y[static 8]);
//
// Standard ARM ABI: X0 = z, X1 = x, X2 = y
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_mul_8_16_neon)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_mul_8_16_neon)
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

// Temporary registers for storing the results from SIMD instructions

#define t0  x25
#define t1  x26
#define t2  x27
#define t3  x28
#define t4  x29
#define t5  x30

// We recycle the input pointers near the end

#define s  x1
#define ud x2


// ---------------------------------------------------------------------------
// The main code
// ---------------------------------------------------------------------------

S2N_BN_SYMBOL(bignum_mul_8_16_neon):

        // Save registers

        sub     sp, sp, #(6*16)
        stp     x19, x20, [sp, #(5*16)]
        stp     x21, x22, [sp, #(4*16)]
        stp     x23, x24, [sp, #(3*16)]
        stp     x25, x26, [sp, #(2*16)]
        stp     x27, x28, [sp, #(1*16)]
        stp     x29, x30, [sp]
        sub     sp, sp, #96

        // Multiply the low halves and then the high halves using ADK 4x4->8.
        // For the second one add the top of the low part (Q1) already into
        // the bottom of the high part (Q2) so that is already dealt with.
        //
        // Write back the first one but defer the second till a bit later while
        // we get on with the absolute difference computations

// NEON: Calculate (x[24] * y[24], x[16] * y[16]), 64x64 -> 64 bit multiplications
ldr   q21, [x, #16]
ldr   q22, [y, #16]

#define in1 v21
#define in2 v22
uzp1 v2.4s, in2.4s, in1.4s
rev64 v1.4s, in2.4s
uzp1 v3.4s, in1.4s, in1.4s
mul v0.4s, v1.4s, in1.4s
uaddlp v0.2d, v0.4s

        ldp     a0, a1, [x]
        ldp     b0, b1, [y]

shl v0.2d, v0.2d, #32
umlal v0.2d, v3.2s, v2.2s
mov t0, v0.d[0] // low64(x[16] * y[16])
mov t1, v0.d[1] // low64(x[24] * y[24])
#undef in1
#undef in2

        ldp     a2, a3, [x, #16]
        ldp     b2, b3, [y, #16]

movi    v19.2d, #0x000000ffffffff

// NEON: Calculate (x[32] * y[32], x[40] * y[40]) for next ADK
ldr   q21, [x, #32]
ldr   q22, [y, #32]

        // First accumulate all the "simple" products as [s7,s6,s5,s4,s0]

        mul     s0, a0, b0
        mul     s4, a1, b1

#define in1  v21
#define in2  v22
#define out_lo v23
#define out_hi v24
uzp2    v3.4s, in2.4s, in1.4s
xtn     v4.2s, in1.2d
xtn     v5.2s, in2.2d
rev64   v1.4s, in2.4s

        umulh   s7, a0, b0
        adds    s4, s4, s7
        umulh   s7, a1, b1
        adcs    s5, t0, s7
        umulh   s7, a2, b2
        adcs    s6, t1, s7
        umulh   s7, a3, b3
        adc     s7, s7, xzr

umull   v6.2d, v4.2s, v5.2s
umull   v7.2d, v4.2s, v3.2s
uzp2    v16.4s, in1.4s, in1.4s
mul     v0.4s, v1.4s, in1.4s
usra    v7.2d, v6.2d, #32
umull   out_hi.2d, v16.2s, v3.2s

        // Multiply by B + 1 to get [s7;s6;s5;s4;s1;s0]

        adds    s1, s4, s0
        adcs    s4, s5, s4
        adcs    s5, s6, s5
        adcs    s6, s7, s6
        adc     s7, xzr, s7

uaddlp  v0.2d, v0.4s
and     v2.16b, v7.16b, v19.16b
umlal   v2.2d, v16.2s, v5.2s
shl     out_lo.2d, v0.2d, #32

        // Multiply by B^2 + 1 to get [s7;s6;s5;s4;s3;s2;s1;s0]

        adds    s2, s4, s0
        adcs    s3, s5, s1
        adcs    s4, s6, s4
        adcs    s5, s7, s5
        adcs    s6, xzr, s6
        adc     s7, xzr, s7

usra    out_hi.2d, v7.2d, #32
umlal   out_lo.2d, v4.2s, v5.2s
mov t0, out_lo.d[0] // low(x[32] * y[32])
mov t1, out_lo.d[1] // low(x[40] * y[40])

        // Now add in all the "complicated" terms.

        muldiffnadd s6,s5, c,h,l,t, a2,a3, b3,b2
        adc     s7, s7, c

usra    out_hi.2d, v2.2d, #32
mov t2, out_hi.d[0] // high(x[32] * y[32])
mov t3, out_hi.d[1] // high(x[40] * y[40])
#undef in1
#undef in2
#undef out_lo
#undef out_hi

// NEON: Calculate (x[48] * y[48], x[56] * y[56]) for next ADK
ldr   q21, [x, #48]
ldr   q22, [y, #48]
#define in1  v21
#define in2  v22
#define out_lo v23
#define out_hi v24
uzp2    v3.4s, in2.4s, in1.4s
xtn     v4.2s, in1.2d
xtn     v5.2s, in2.2d
rev64   v1.4s, in2.4s

        muldiffnadd s2,s1, c,h,l,t, a0,a1, b1,b0

umull   v6.2d, v4.2s, v5.2s
umull   v7.2d, v4.2s, v3.2s
uzp2    v16.4s, in1.4s, in1.4s

        adcs    s3, s3, c
        adcs    s4, s4, c
        adcs    s5, s5, c
        adcs    s6, s6, c
        adc     s7, s7, c

mul     v0.4s, v1.4s, in1.4s
usra    v7.2d, v6.2d, #32
umull   out_hi.2d, v16.2s, v3.2s

        muldiffnadd s5,s4, c,h,l,t, a1,a3, b3,b1

uaddlp  v0.2d, v0.4s
and     v2.16b, v7.16b, v19.16b

        adcs    s6, s6, c
        adc     s7, s7, c

umlal   v2.2d, v16.2s, v5.2s
shl     out_lo.2d, v0.2d, #32

        muldiffnadd s3,s2, c,h,l,t, a0,a2, b2,b0
        adcs    s4, s4, c
        adcs    s5, s5, c
        adcs    s6, s6, c
        adc     s7, s7, c

usra    out_hi.2d, v7.2d, #32
umlal   out_lo.2d, v4.2s, v5.2s
mov t4, out_lo.d[0] // low64(x[48] * y[48])
mov t5, out_lo.d[1] // low64(x[56] * y[56])

        stp     s0, s1, [z]

        muldiffnadd s4,s3, c,h,l,t, a0,a3, b3,b0
        adcs    s5, s5, c
        adcs    s6, s6, c
        adc     s7, s7, c

usra    out_hi.2d, v2.2d, #32

        muldiffnadd s4,s3, c,h,l,t, a1,a2, b2,b1

mov s0, out_hi.d[0] // high64(x[48]*y[48])

        adcs    s5, s5, c
        adcs    s6, s6, c
        adc     s7, s7, c

mov s1, out_hi.d[1] // high64(x[56]*y[56])
#undef in1
#undef in2
#undef out_lo
#undef out_hi

        stp     s2, s3, [z, #16]
        stp     s4, s5, [z, #32]
        stp     s6, s7, [z, #48]

        // Now ADK for high parts.

        ldp     a0, a1, [x, #32]
        ldp     a2, a3, [x, #48]
        ldp     b0, b1, [y, #32]
        ldp     b2, b3, [y, #48]

        // Prepare the final ADK in advance which needs x[63:32] - x[31:0] and y[63:32] - y[31:0]
        ldp     l, h, [x]
        ldp     c, m, [x, #16]
        subs    l, a0, l
        sbcs    h, a1, h
        sbcs    c, a2, c
        sbcs    m, a3, m
        csetm   t, cc

        eor     l, l, t
        subs    l, l, t
        eor     h, h, t
        sbcs    h, h, t
        eor     c, c, t
        sbcs    c, c, t
        eor     m, m, t
        sbc     m, m, t

        stp     l, h, [sp]
        stp     c, m, [sp, #16]
        stp     t, xzr, [sp, #32]

ldr   q21, [sp]
ldr   q25, [sp, #16]

        ldp     l, h, [y]
        ldp     c, m, [y, #16]
        subs    l, l, b0
        sbcs    h, h, b1
        sbcs    c, c, b2
        sbcs    m, m, b3
        csetm   t, cc
        eor     l, l, t
        subs    l, l, t
        eor     h, h, t
        sbcs    h, h, t
        eor     c, c, t
        sbcs    c, c, t
        eor     m, m, t
        sbc     m, m, t

        stp     l, h, [sp, #48]
        stp     c, m, [sp, #64]
        stp     t, xzr, [sp, #80]

ldr   q22, [sp, #48]
ldr   q26, [sp, #64]

        // Now restart the ADK for high parts.

        adds    s4, t1, t2
        adcs    s5, t4, t3
        adcs    s6, t5, s0
        adc     s7, s1, xzr

#define in1  v21
#define in2  v22
#define out_lo v23
#define out_hi v24
uzp2    v3.4s, in2.4s, in1.4s
xtn     v4.2s, in1.2d

        adds    s1, s4, t0
        adcs    s4, s5, s4
        adcs    s5, s6, s5
        adcs    s6, s7, s6
        adc     s7, xzr, s7

xtn     v5.2s, in2.2d
rev64   v1.4s, in2.4s

        adds    s2, s4, t0
        adcs    s3, s5, s1
        adcs    s4, s6, s4

umull   v6.2d, v4.2s, v5.2s
umull   v7.2d, v4.2s, v3.2s

        adcs    s5, s7, s5
        adcs    s6, xzr, s6
        adc     s7, xzr, s7

uzp2    v16.4s, in1.4s, in1.4s
mul     v0.4s, v1.4s, in1.4s

        ldp     l, h, [z,#32]

usra    v7.2d, v6.2d, #32
umull   out_hi.2d, v16.2s, v3.2s

        adds    s0, t0, l
        adcs    s1, s1, h

uaddlp  v0.2d, v0.4s

        ldp     l, h, [z,#48]

and     v2.16b, v7.16b, v19.16b

        adcs    s2, s2, l
        adcs    s3, s3, h

umlal   v2.2d, v16.2s, v5.2s

        adcs    s4, s4, xzr
        adcs    s5, s5, xzr

shl     out_lo.2d, v0.2d, #32

        adcs    s6, s6, xzr
        adc     s7, s7, xzr

usra    out_hi.2d, v7.2d, #32
umlal   out_lo.2d, v4.2s, v5.2s
usra    out_hi.2d, v2.2d, #32
#undef in1
#undef in2
#undef out_lo
#undef out_hi

        muldiffnadd s6,s5, c,h,l,t, a2,a3, b3,b2

mov t5, v24.d[0] // out_hi.d[0]

        adc     s7, s7, c

#define in1  v25
#define in2  v26
#define out_lo v27
#define out_hi v28
uzp2    v3.4s, in2.4s, in1.4s
xtn     v4.2s, in1.2d
xtn     v5.2s, in2.2d

        muldiffnadd s2,s1, c,h,l,t, a0,a1, b1,b0

rev64   v1.4s, in2.4s
umull   v6.2d, v4.2s, v5.2s

        adcs    s3, s3, c
        adcs    s4, s4, c
        adcs    s5, s5, c
        adcs    s6, s6, c
        adc     s7, s7, c

umull   v7.2d, v4.2s, v3.2s
uzp2    v16.4s, in1.4s, in1.4s
mul     v0.4s, v1.4s, in1.4s
usra    v7.2d, v6.2d, #32
umull   out_hi.2d, v16.2s, v3.2s
uaddlp  v0.2d, v0.4s
and     v2.16b, v7.16b, v19.16b

        muldiffnadd s5,s4, c,h,l,t, a1,a3, b3,b1

umlal   v2.2d, v16.2s, v5.2s

        adcs    s6, s6, c
        adc     s7, s7, c

shl     out_lo.2d, v0.2d, #32
usra    out_hi.2d, v7.2d, #32
umlal   out_lo.2d, v4.2s, v5.2s
usra    out_hi.2d, v2.2d, #32

        muldiffnadd s3,s2, c,h,l,t, a0,a2, b2,b0

mov t0, v23.d[1] // out_lo.d[1]

        adcs    s4, s4, c
        adcs    s5, s5, c
        adcs    s6, s6, c
        adc     s7, s7, c

mov t4, v27.d[0]

        muldiffnadd s4,s3, c,h,l,t, a0,a3, b3,b0

mov t3, v24.d[1] // out_hi.d[1]

        adcs    s5, s5, c
        adcs    s6, s6, c
        adc     s7, s7, c

mov t1, out_lo.d[1]

        muldiffnadd s4,s3, c,h,l,t, a1,a2, b2,b1

mov t2, v28.d[0]

        adcs    s5, s5, c
        adcs    s6, s6, c
        adc     s7, s7, c

#undef in1
#undef in2
#undef out_lo
#undef out_hi

mov h, v28.d[1]

        stp     s0, s1, [z, #64]

mov s0, v23.d[0] // out_lo.d[0]

        stp     s2, s3, [z, #80]
        stp     s4, s5, [z, #96]
        stp     s6, s7, [z, #112]

        // Compute t,[a3,a2,a1,a0] = x_hi - x_lo
        // and     s,[b3,b2,b1,b0] = y_lo - y_hi
        // sign-magnitude differences, and scatter in belated high writeback

        ldp     a0, a1, [sp]
        ldp     a2, a3, [sp, #16]
        ldp     t, xzr, [sp, #32]
        ldp     b0, b1, [sp, #48]
        ldp     b2, b3, [sp, #64]
        ldp     s, xzr, [sp, #80]

        // Save the correct sign for the sub-product

        eor     s, s, t

        // Now yet another 4x4->8 ADK core, but not writing back, keeping s0..s7

        adds    s4, t0, t5
        adcs    s5, t4, t3
        adcs    s6, t1, t2
        adc     s7, h, xzr

        adds    s1, s4, s0
        adcs    s4, s5, s4
        adcs    s5, s6, s5
        adcs    s6, s7, s6
        adc     s7, xzr, s7

        adds    s2, s4, s0
        adcs    s3, s5, s1
        adcs    s4, s6, s4
        adcs    s5, s7, s5
        adcs    s6, xzr, s6
        adc     s7, xzr, s7

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

        // Now accumulate the positive mid-terms as [u7,u6,u5,u4,u3.u2,u1,u0]

        ldp     u0, u1, [z]
        ldp     u4, u5, [z,#64]
        adds    u0, u0, u4
        adcs    u1, u1, u5
        ldp     u2, u3, [z,#16]
        ldp     u6, u7, [z,#80]
        adcs    u2, u2, u6
        adcs    u3, u3, u7
        ldp     u8, u9, [z,#96]
        adcs    u4, u4, u8
        adcs    u5, u5, u9
        ldp     u10, u11, [z,#112]
        adcs    u6, u6, u10
        adcs    u7, u7, u11

// Stop the carry here so we can reintroduce it, taking into account the
// effective addition of s from sign-extension below. Note that we get
// a duplicated word c+carry beyond the first one, so this upper part is
// of the form [ud,ud,ud,t].

        adcs    t, s, xzr
        adc     ud, s, xzr

// Add in the sign-adjusted complex term

        adds    xzr, s, #1
        eor     s0, s0, s
        adcs    u0, s0, u0
        eor     s1, s1, s
        adcs    u1, s1, u1
        eor     s2, s2, s
        adcs    u2, s2, u2
        eor     s3, s3, s
        adcs    u3, s3, u3
        eor     s4, s4, s
        adcs    u4, s4, u4
        eor     s5, s5, s
        adcs    u5, s5, u5
        eor     s6, s6, s
        adcs    u6, s6, u6
        eor     s7, s7, s
        adcs    u7, s7, u7

// From this point on replace the sign with the suspended carry indication

        adcs    u8, u8, t
        adcs    u9, u9, ud
        adcs    u10, u10, ud
        adc     u11, u11, ud

// Store it back

        stp     u0, u1, [z,#32]
        stp     u2, u3, [z,#48]
        stp     u4, u5, [z,#64]
        stp     u6, u7, [z,#80]
        stp     u8, u9, [z,#96]
        stp     u10, u11, [z,#112]

// Restore regs and return

        add     sp, sp, #96
        ldp     x29, x30, [sp]
        ldp     x27, x28, [sp, #(1*16)]
        ldp     x25, x26, [sp, #(2*16)]
        ldp     x23, x24, [sp, #(3*16)]
        ldp     x21, x22, [sp, #(4*16)]
        ldp     x19, x20, [sp, #(5*16)]
        add sp, sp, #(6*16)

        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
