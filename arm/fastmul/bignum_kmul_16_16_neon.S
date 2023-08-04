// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// ----------------------------------------------------------------------------
// Multiply z := x * y
// Inputs x[16], y[16]; output z[16]; temporary buffer t[>=16]
//
//    extern void bignum_kmul_16_16_neon
//     (uint64_t z[static 16], uint64_t x[static 16], uint64_t y[static 16],
//      uint64_t t[static 16])
//
// This is a Karatsuba-style function multiplying half-sized results
// internally and using temporary buffer t for intermediate results.
//
// Standard ARM ABI: X0 = z, X1 = x, X2 = y, X3 = t
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_kmul_16_16_neon)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_kmul_16_16_neon)
        .text
        .balign 4

// Subroutine-safe copies of the output, inputs and temporary buffer pointers

#define z x25
#define x x26
#define y x27
#define t x28

// More variables for sign masks, with s also necessarily subroutine-safe

#define s x29
#define m x19

S2N_BN_SYMBOL(bignum_kmul_16_16_neon):

// Save registers, including return address

        stp     x19, x20, [sp, #-16]!
        stp     x21, x22, [sp, #-16]!
        stp     x23, x24, [sp, #-16]!
        stp     x25, x26, [sp, #-16]!
        stp     x27, x28, [sp, #-16]!
        stp     x29, x30, [sp, #-16]!

// Move parameters into subroutine-safe places

        mov     z, x0
        mov     x, x1
        mov     y, x2
        mov     t, x3

// Compute L = x_lo * y_lo in bottom half of z (size 8 x 8 -> 16)

        bl      bignum_kmul_16_32_neon_local_mul_8_16

// Compute H = x_hi * y_lo in t (size 8 x 8 -> 16)

        mov     x0, t
        add     x1, x, #64
        mov     x2, y
        bl      bignum_kmul_16_32_neon_local_mul_8_8

        ldp     x10, x11, [t]
        ldp     x12, x13, [z, #64]
        adds    x12, x12, x10
        adcs    x13, x13, x11
        stp     x12, x13, [z, #64]

        ldp     x10, x11, [t, #16]
        ldp     x12, x13, [z, #80]
        adcs    x12, x12, x10
        adcs    x13, x13, x11
        stp     x12, x13, [z, #80]

        ldp     x10, x11, [t, #32]
        ldp     x12, x13, [z, #96]
        adcs    x12, x12, x10
        adcs    x13, x13, x11
        stp     x12, x13, [z, #96]

        ldp     x10, x11, [t, #48]
        ldp     x12, x13, [z, #112]
        adcs    x12, x12, x10
        adc     x13, x13, x11
        stp     x12, x13, [z, #112]

// Compute H = x_lo * y_hi in t (size 8 x 8 -> 16)

        mov     x0, t
        mov     x1, x
        add     x2, y, #64
        bl      bignum_kmul_16_32_neon_local_mul_8_8

        ldp     x10, x11, [t]
        ldp     x12, x13, [z, #64]
        adds    x12, x12, x10
        adcs    x13, x13, x11
        stp     x12, x13, [z, #64]

        ldp     x10, x11, [t, #16]
        ldp     x12, x13, [z, #80]
        adcs    x12, x12, x10
        adcs    x13, x13, x11
        stp     x12, x13, [z, #80]

        ldp     x10, x11, [t, #32]
        ldp     x12, x13, [z, #96]
        adcs    x12, x12, x10
        adcs    x13, x13, x11
        stp     x12, x13, [z, #96]

        ldp     x10, x11, [t, #48]
        ldp     x12, x13, [z, #112]
        adcs    x12, x12, x10
        adc     x13, x13, x11
        stp     x12, x13, [z, #112]

// Restore registers and return

        ldp     x29, x30, [sp], #16
        ldp     x27, x28, [sp], #16
        ldp     x25, x26, [sp], #16
        ldp     x23, x24, [sp], #16
        ldp     x21, x22, [sp], #16
        ldp     x19, x20, [sp], #16

        ret

// ----------------------------------------------------------------------------
// Local copy of bignum_mul_8_16_neon without the scratch register save/restore
// ----------------------------------------------------------------------------

bignum_kmul_16_32_neon_local_mul_8_16:
        stp	x25, x26, [sp, #-16]!
        stp	x27, x28, [sp, #-16]!
        stp	x29, x30, [sp, #-16]!
        sub	sp, sp, #0x60
        ldr	q21, [x1, #16]
        ldr	q22, [x2, #16]
        uzp1	v2.4s, v22.4s, v21.4s
        rev64	v1.4s, v22.4s
        uzp1	v3.4s, v21.4s, v21.4s
        mul	v0.4s, v1.4s, v21.4s
        uaddlp	v0.2d, v0.4s
        ldp	x3, x4, [x1]
        ldp	x7, x8, [x2]
        shl	v0.2d, v0.2d, #32
        umlal	v0.2d, v3.2s, v2.2s
        mov	x25, v0.d[0]
        mov	x26, v0.d[1]
        ldp	x5, x6, [x1, #16]
        ldp	x9, x10, [x2, #16]
        movi	v19.2d, #0xffffffff
        ldr	q21, [x1, #32]
        ldr	q22, [x2, #32]
        mul	x11, x3, x7
        mul	x15, x4, x8
        uzp2	v3.4s, v22.4s, v21.4s
        xtn	v4.2s, v21.2d
        xtn	v5.2s, v22.2d
        rev64	v1.4s, v22.4s
        umulh	x19, x3, x7
        adds	x15, x15, x19
        umulh	x19, x4, x8
        adcs	x16, x25, x19
        umulh	x19, x5, x9
        adcs	x17, x26, x19
        umulh	x19, x6, x10
        adc	x19, x19, xzr
        umull	v6.2d, v4.2s, v5.2s
        umull	v7.2d, v4.2s, v3.2s
        uzp2	v16.4s, v21.4s, v21.4s
        mul	v0.4s, v1.4s, v21.4s
        usra	v7.2d, v6.2d, #32
        umull	v24.2d, v16.2s, v3.2s
        adds	x12, x15, x11
        adcs	x15, x16, x15
        adcs	x16, x17, x16
        adcs	x17, x19, x17
        adc	x19, xzr, x19
        uaddlp	v0.2d, v0.4s
        and	v2.16b, v7.16b, v19.16b
        umlal	v2.2d, v16.2s, v5.2s
        shl	v23.2d, v0.2d, #32
        adds	x13, x15, x11
        adcs	x14, x16, x12
        adcs	x15, x17, x15
        adcs	x16, x19, x16
        adcs	x17, xzr, x17
        adc	x19, xzr, x19
        usra	v24.2d, v7.2d, #32
        umlal	v23.2d, v4.2s, v5.2s
        mov	x25, v23.d[0]
        mov	x26, v23.d[1]
        subs	x24, x5, x6
        cneg	x24, x24, cc  // cc = lo, ul, last
        csetm	x20, cc  // cc = lo, ul, last
        subs	x21, x10, x9
        cneg	x21, x21, cc  // cc = lo, ul, last
        mul	x22, x24, x21
        umulh	x21, x24, x21
        cinv	x20, x20, cc  // cc = lo, ul, last
        cmn	x20, #0x1
        eor	x22, x22, x20
        adcs	x16, x16, x22
        eor	x21, x21, x20
        adcs	x17, x17, x21
        adc	x19, x19, x20
        usra	v24.2d, v2.2d, #32
        mov	x27, v24.d[0]
        mov	x28, v24.d[1]
        ldr	q21, [x1, #48]
        ldr	q22, [x2, #48]
        uzp2	v3.4s, v22.4s, v21.4s
        xtn	v4.2s, v21.2d
        xtn	v5.2s, v22.2d
        rev64	v1.4s, v22.4s
        subs	x24, x3, x4
        cneg	x24, x24, cc  // cc = lo, ul, last
        csetm	x20, cc  // cc = lo, ul, last
        subs	x21, x8, x7
        cneg	x21, x21, cc  // cc = lo, ul, last
        mul	x22, x24, x21
        umulh	x21, x24, x21
        cinv	x20, x20, cc  // cc = lo, ul, last
        cmn	x20, #0x1
        eor	x22, x22, x20
        adcs	x12, x12, x22
        eor	x21, x21, x20
        adcs	x13, x13, x21
        umull	v6.2d, v4.2s, v5.2s
        umull	v7.2d, v4.2s, v3.2s
        uzp2	v16.4s, v21.4s, v21.4s
        adcs	x14, x14, x20
        adcs	x15, x15, x20
        adcs	x16, x16, x20
        adcs	x17, x17, x20
        adc	x19, x19, x20
        mul	v0.4s, v1.4s, v21.4s
        usra	v7.2d, v6.2d, #32
        umull	v24.2d, v16.2s, v3.2s
        subs	x24, x4, x6
        cneg	x24, x24, cc  // cc = lo, ul, last
        csetm	x20, cc  // cc = lo, ul, last
        subs	x21, x10, x8
        cneg	x21, x21, cc  // cc = lo, ul, last
        mul	x22, x24, x21
        umulh	x21, x24, x21
        cinv	x20, x20, cc  // cc = lo, ul, last
        cmn	x20, #0x1
        eor	x22, x22, x20
        adcs	x15, x15, x22
        eor	x21, x21, x20
        adcs	x16, x16, x21
        uaddlp	v0.2d, v0.4s
        and	v2.16b, v7.16b, v19.16b
        adcs	x17, x17, x20
        adc	x19, x19, x20
        umlal	v2.2d, v16.2s, v5.2s
        shl	v23.2d, v0.2d, #32
        subs	x24, x3, x5
        cneg	x24, x24, cc  // cc = lo, ul, last
        csetm	x20, cc  // cc = lo, ul, last
        subs	x21, x9, x7
        cneg	x21, x21, cc  // cc = lo, ul, last
        mul	x22, x24, x21
        umulh	x21, x24, x21
        cinv	x20, x20, cc  // cc = lo, ul, last
        cmn	x20, #0x1
        eor	x22, x22, x20
        adcs	x13, x13, x22
        eor	x21, x21, x20
        adcs	x14, x14, x21
        adcs	x15, x15, x20
        adcs	x16, x16, x20
        adcs	x17, x17, x20
        adc	x19, x19, x20
        usra	v24.2d, v7.2d, #32
        umlal	v23.2d, v4.2s, v5.2s
        mov	x29, v23.d[0]
        mov	x30, v23.d[1]
        stp	x11, x12, [x0]
        subs	x24, x3, x6
        cneg	x24, x24, cc  // cc = lo, ul, last
        csetm	x20, cc  // cc = lo, ul, last
        subs	x21, x10, x7
        cneg	x21, x21, cc  // cc = lo, ul, last
        mul	x22, x24, x21
        umulh	x21, x24, x21
        cinv	x20, x20, cc  // cc = lo, ul, last
        cmn	x20, #0x1
        eor	x22, x22, x20
        adcs	x14, x14, x22
        eor	x21, x21, x20
        adcs	x15, x15, x21
        adcs	x16, x16, x20
        adcs	x17, x17, x20
        adc	x19, x19, x20
        usra	v24.2d, v2.2d, #32
        subs	x24, x4, x5
        cneg	x24, x24, cc  // cc = lo, ul, last
        csetm	x20, cc  // cc = lo, ul, last
        subs	x21, x9, x8
        cneg	x21, x21, cc  // cc = lo, ul, last
        mul	x22, x24, x21
        umulh	x21, x24, x21
        cinv	x20, x20, cc  // cc = lo, ul, last
        cmn	x20, #0x1
        eor	x22, x22, x20
        adcs	x14, x14, x22
        eor	x21, x21, x20
        adcs	x15, x15, x21
        mov	x11, v24.d[0]
        adcs	x16, x16, x20
        adcs	x17, x17, x20
        adc	x19, x19, x20
        mov	x12, v24.d[1]
        stp	x13, x14, [x0, #16]
        stp	x15, x16, [x0, #32]
        stp	x17, x19, [x0, #48]
        ldp	x3, x4, [x1, #32]
        ldp	x5, x6, [x1, #48]
        ldp	x7, x8, [x2, #32]
        ldp	x9, x10, [x2, #48]
        ldp	x22, x21, [x1]
        ldp	x20, x23, [x1, #16]
        subs	x22, x3, x22
        sbcs	x21, x4, x21
        sbcs	x20, x5, x20
        sbcs	x23, x6, x23
        csetm	x24, cc  // cc = lo, ul, last
        eor	x22, x22, x24
        subs	x22, x22, x24
        eor	x21, x21, x24
        sbcs	x21, x21, x24
        eor	x20, x20, x24
        sbcs	x20, x20, x24
        eor	x23, x23, x24
        sbc	x23, x23, x24
        stp	x22, x21, [sp]
        stp	x20, x23, [sp, #16]
        stp	x24, xzr, [sp, #32]
        ldr	q21, [sp]
        ldr	q25, [sp, #16]
        ldp	x22, x21, [x2]
        ldp	x20, x23, [x2, #16]
        subs	x22, x22, x7
        sbcs	x21, x21, x8
        sbcs	x20, x20, x9
        sbcs	x23, x23, x10
        csetm	x24, cc  // cc = lo, ul, last
        eor	x22, x22, x24
        subs	x22, x22, x24
        eor	x21, x21, x24
        sbcs	x21, x21, x24
        eor	x20, x20, x24
        sbcs	x20, x20, x24
        eor	x23, x23, x24
        sbc	x23, x23, x24
        stp	x22, x21, [sp, #48]
        stp	x20, x23, [sp, #64]
        stp	x24, xzr, [sp, #80]
        ldr	q22, [sp, #48]
        ldr	q26, [sp, #64]
        adds	x15, x26, x27
        adcs	x16, x29, x28
        adcs	x17, x30, x11
        adc	x19, x12, xzr
        uzp2	v3.4s, v22.4s, v21.4s
        xtn	v4.2s, v21.2d
        adds	x12, x15, x25
        adcs	x15, x16, x15
        adcs	x16, x17, x16
        adcs	x17, x19, x17
        adc	x19, xzr, x19
        xtn	v5.2s, v22.2d
        rev64	v1.4s, v22.4s
        adds	x13, x15, x25
        adcs	x14, x16, x12
        adcs	x15, x17, x15
        umull	v6.2d, v4.2s, v5.2s
        umull	v7.2d, v4.2s, v3.2s
        adcs	x16, x19, x16
        adcs	x17, xzr, x17
        adc	x19, xzr, x19
        uzp2	v16.4s, v21.4s, v21.4s
        mul	v0.4s, v1.4s, v21.4s
        ldp	x22, x21, [x0, #32]
        usra	v7.2d, v6.2d, #32
        umull	v24.2d, v16.2s, v3.2s
        adds	x11, x25, x22
        adcs	x12, x12, x21
        uaddlp	v0.2d, v0.4s
        ldp	x22, x21, [x0, #48]
        and	v2.16b, v7.16b, v19.16b
        adcs	x13, x13, x22
        adcs	x14, x14, x21
        umlal	v2.2d, v16.2s, v5.2s
        adcs	x15, x15, xzr
        adcs	x16, x16, xzr
        shl	v23.2d, v0.2d, #32
        adcs	x17, x17, xzr
        adc	x19, x19, xzr
        usra	v24.2d, v7.2d, #32
        umlal	v23.2d, v4.2s, v5.2s
        usra	v24.2d, v2.2d, #32
        subs	x24, x5, x6
        cneg	x24, x24, cc  // cc = lo, ul, last
        csetm	x20, cc  // cc = lo, ul, last
        subs	x21, x10, x9
        cneg	x21, x21, cc  // cc = lo, ul, last
        mul	x22, x24, x21
        umulh	x21, x24, x21
        cinv	x20, x20, cc  // cc = lo, ul, last
        cmn	x20, #0x1
        eor	x22, x22, x20
        adcs	x16, x16, x22
        eor	x21, x21, x20
        adcs	x17, x17, x21
        mov	x30, v24.d[0]
        adc	x19, x19, x20
        uzp2	v3.4s, v26.4s, v25.4s
        xtn	v4.2s, v25.2d
        xtn	v5.2s, v26.2d
        subs	x24, x3, x4
        cneg	x24, x24, cc  // cc = lo, ul, last
        csetm	x20, cc  // cc = lo, ul, last
        subs	x21, x8, x7
        cneg	x21, x21, cc  // cc = lo, ul, last
        mul	x22, x24, x21
        umulh	x21, x24, x21
        cinv	x20, x20, cc  // cc = lo, ul, last
        cmn	x20, #0x1
        eor	x22, x22, x20
        adcs	x12, x12, x22
        eor	x21, x21, x20
        adcs	x13, x13, x21
        rev64	v1.4s, v26.4s
        umull	v6.2d, v4.2s, v5.2s
        adcs	x14, x14, x20
        adcs	x15, x15, x20
        adcs	x16, x16, x20
        adcs	x17, x17, x20
        adc	x19, x19, x20
        umull	v7.2d, v4.2s, v3.2s
        uzp2	v16.4s, v25.4s, v25.4s
        mul	v0.4s, v1.4s, v25.4s
        usra	v7.2d, v6.2d, #32
        subs	x24, x4, x6
        cneg	x24, x24, cc  // cc = lo, ul, last
        csetm	x20, cc  // cc = lo, ul, last
        subs	x21, x10, x8
        cneg	x21, x21, cc  // cc = lo, ul, last
        mul	x22, x24, x21
        umulh	x21, x24, x21
        cinv	x20, x20, cc  // cc = lo, ul, last
        cmn	x20, #0x1
        eor	x22, x22, x20
        adcs	x15, x15, x22
        eor	x21, x21, x20
        adcs	x16, x16, x21
        umull	v28.2d, v16.2s, v3.2s
        uaddlp	v0.2d, v0.4s
        and	v2.16b, v7.16b, v19.16b
        umlal	v2.2d, v16.2s, v5.2s
        adcs	x17, x17, x20
        adc	x19, x19, x20
        shl	v27.2d, v0.2d, #32
        usra	v28.2d, v7.2d, #32
        umlal	v27.2d, v4.2s, v5.2s
        usra	v28.2d, v2.2d, #32
        subs	x24, x3, x5
        cneg	x24, x24, cc  // cc = lo, ul, last
        csetm	x20, cc  // cc = lo, ul, last
        subs	x21, x9, x7
        cneg	x21, x21, cc  // cc = lo, ul, last
        mul	x22, x24, x21
        umulh	x21, x24, x21
        cinv	x20, x20, cc  // cc = lo, ul, last
        cmn	x20, #0x1
        eor	x22, x22, x20
        adcs	x13, x13, x22
        eor	x21, x21, x20
        adcs	x14, x14, x21
        mov	x25, v23.d[1]
        adcs	x15, x15, x20
        adcs	x16, x16, x20
        adcs	x17, x17, x20
        adc	x19, x19, x20
        mov	x29, v27.d[0]
        subs	x24, x3, x6
        cneg	x24, x24, cc  // cc = lo, ul, last
        csetm	x20, cc  // cc = lo, ul, last
        subs	x21, x10, x7
        cneg	x21, x21, cc  // cc = lo, ul, last
        mul	x22, x24, x21
        umulh	x21, x24, x21
        cinv	x20, x20, cc  // cc = lo, ul, last
        cmn	x20, #0x1
        eor	x22, x22, x20
        adcs	x14, x14, x22
        eor	x21, x21, x20
        adcs	x15, x15, x21
        mov	x28, v24.d[1]
        adcs	x16, x16, x20
        adcs	x17, x17, x20
        adc	x19, x19, x20
        mov	x26, v27.d[1]
        subs	x24, x4, x5
        cneg	x24, x24, cc  // cc = lo, ul, last
        csetm	x20, cc  // cc = lo, ul, last
        subs	x21, x9, x8
        cneg	x21, x21, cc  // cc = lo, ul, last
        mul	x22, x24, x21
        umulh	x21, x24, x21
        cinv	x20, x20, cc  // cc = lo, ul, last
        cmn	x20, #0x1
        eor	x22, x22, x20
        adcs	x14, x14, x22
        eor	x21, x21, x20
        adcs	x15, x15, x21
        mov	x27, v28.d[0]
        adcs	x16, x16, x20
        adcs	x17, x17, x20
        adc	x19, x19, x20
        mov	x21, v28.d[1]
        stp	x11, x12, [x0, #64]
        mov	x11, v23.d[0]
        stp	x13, x14, [x0, #80]
        stp	x15, x16, [x0, #96]
        stp	x17, x19, [x0, #112]
        ldp	x3, x4, [sp]
        ldp	x5, x6, [sp, #16]
        ldp	x24, xzr, [sp, #32]
        ldp	x7, x8, [sp, #48]
        ldp	x9, x10, [sp, #64]
        ldp	x1, xzr, [sp, #80]
        eor	x1, x1, x24
        adds	x15, x25, x30
        adcs	x16, x29, x28
        adcs	x17, x26, x27
        adc	x19, x21, xzr
        adds	x12, x15, x11
        adcs	x15, x16, x15
        adcs	x16, x17, x16
        adcs	x17, x19, x17
        adc	x19, xzr, x19
        adds	x13, x15, x11
        adcs	x14, x16, x12
        adcs	x15, x17, x15
        adcs	x16, x19, x16
        adcs	x17, xzr, x17
        adc	x19, xzr, x19
        subs	x24, x5, x6
        cneg	x24, x24, cc  // cc = lo, ul, last
        csetm	x20, cc  // cc = lo, ul, last
        subs	x21, x10, x9
        cneg	x21, x21, cc  // cc = lo, ul, last
        mul	x22, x24, x21
        umulh	x21, x24, x21
        cinv	x20, x20, cc  // cc = lo, ul, last
        cmn	x20, #0x1
        eor	x22, x22, x20
        adcs	x16, x16, x22
        eor	x21, x21, x20
        adcs	x17, x17, x21
        adc	x19, x19, x20
        subs	x24, x3, x4
        cneg	x24, x24, cc  // cc = lo, ul, last
        csetm	x20, cc  // cc = lo, ul, last
        subs	x21, x8, x7
        cneg	x21, x21, cc  // cc = lo, ul, last
        mul	x22, x24, x21
        umulh	x21, x24, x21
        cinv	x20, x20, cc  // cc = lo, ul, last
        cmn	x20, #0x1
        eor	x22, x22, x20
        adcs	x12, x12, x22
        eor	x21, x21, x20
        adcs	x13, x13, x21
        adcs	x14, x14, x20
        adcs	x15, x15, x20
        adcs	x16, x16, x20
        adcs	x17, x17, x20
        adc	x19, x19, x20
        subs	x24, x4, x6
        cneg	x24, x24, cc  // cc = lo, ul, last
        csetm	x20, cc  // cc = lo, ul, last
        subs	x21, x10, x8
        cneg	x21, x21, cc  // cc = lo, ul, last
        mul	x22, x24, x21
        umulh	x21, x24, x21
        cinv	x20, x20, cc  // cc = lo, ul, last
        cmn	x20, #0x1
        eor	x22, x22, x20
        adcs	x15, x15, x22
        eor	x21, x21, x20
        adcs	x16, x16, x21
        adcs	x17, x17, x20
        adc	x19, x19, x20
        subs	x24, x3, x5
        cneg	x24, x24, cc  // cc = lo, ul, last
        csetm	x20, cc  // cc = lo, ul, last
        subs	x21, x9, x7
        cneg	x21, x21, cc  // cc = lo, ul, last
        mul	x22, x24, x21
        umulh	x21, x24, x21
        cinv	x20, x20, cc  // cc = lo, ul, last
        cmn	x20, #0x1
        eor	x22, x22, x20
        adcs	x13, x13, x22
        eor	x21, x21, x20
        adcs	x14, x14, x21
        adcs	x15, x15, x20
        adcs	x16, x16, x20
        adcs	x17, x17, x20
        adc	x19, x19, x20
        subs	x24, x3, x6
        cneg	x24, x24, cc  // cc = lo, ul, last
        csetm	x20, cc  // cc = lo, ul, last
        subs	x21, x10, x7
        cneg	x21, x21, cc  // cc = lo, ul, last
        mul	x22, x24, x21
        umulh	x21, x24, x21
        cinv	x20, x20, cc  // cc = lo, ul, last
        cmn	x20, #0x1
        eor	x22, x22, x20
        adcs	x14, x14, x22
        eor	x21, x21, x20
        adcs	x15, x15, x21
        adcs	x16, x16, x20
        adcs	x17, x17, x20
        adc	x19, x19, x20
        subs	x24, x4, x5
        cneg	x24, x24, cc  // cc = lo, ul, last
        csetm	x20, cc  // cc = lo, ul, last
        subs	x21, x9, x8
        cneg	x21, x21, cc  // cc = lo, ul, last
        mul	x22, x24, x21
        umulh	x21, x24, x21
        cinv	x20, x20, cc  // cc = lo, ul, last
        cmn	x20, #0x1
        eor	x22, x22, x20
        adcs	x14, x14, x22
        eor	x21, x21, x20
        adcs	x15, x15, x21
        adcs	x16, x16, x20
        adcs	x17, x17, x20
        adc	x19, x19, x20
        ldp	x3, x4, [x0]
        ldp	x7, x8, [x0, #64]
        adds	x3, x3, x7
        adcs	x4, x4, x8
        ldp	x5, x6, [x0, #16]
        ldp	x9, x10, [x0, #80]
        adcs	x5, x5, x9
        adcs	x6, x6, x10
        ldp	x20, x21, [x0, #96]
        adcs	x7, x7, x20
        adcs	x8, x8, x21
        ldp	x22, x23, [x0, #112]
        adcs	x9, x9, x22
        adcs	x10, x10, x23
        adcs	x24, x1, xzr
        adc	x2, x1, xzr
        cmn	x1, #0x1
        eor	x11, x11, x1
        adcs	x3, x11, x3
        eor	x12, x12, x1
        adcs	x4, x12, x4
        eor	x13, x13, x1
        adcs	x5, x13, x5
        eor	x14, x14, x1
        adcs	x6, x14, x6
        eor	x15, x15, x1
        adcs	x7, x15, x7
        eor	x16, x16, x1
        adcs	x8, x16, x8
        eor	x17, x17, x1
        adcs	x9, x17, x9
        eor	x19, x19, x1
        adcs	x10, x19, x10
        adcs	x20, x20, x24
        adcs	x21, x21, x2
        adcs	x22, x22, x2
        adc	x23, x23, x2
        stp	x3, x4, [x0, #32]
        stp	x5, x6, [x0, #48]
        stp	x7, x8, [x0, #64]
        stp	x9, x10, [x0, #80]
        stp	x20, x21, [x0, #96]
        stp	x22, x23, [x0, #112]
        add	sp, sp, #0x60
        ldp	x29, x30, [sp], #16
        ldp	x27, x28, [sp], #16
        ldp	x25, x26, [sp], #16
        ret


bignum_kmul_16_32_neon_local_mul_8_8:
        stp	x25, x26, [sp, #-16]!
        stp	x27, x28, [sp, #-16]!
        stp	x29, x30, [sp, #-16]!
        movi	v19.2d, #0xffffffff
        ldr	q21, [x1, #16]
        ldr	q22, [x2, #16]
        uzp2	v3.4s, v22.4s, v21.4s
        xtn	v4.2s, v21.2d
        xtn	v5.2s, v22.2d
        rev64	v1.4s, v22.4s
        ldp	x3, x4, [x1]
        ldp	x7, x8, [x2]
        umull	v6.2d, v4.2s, v5.2s
        umull	v7.2d, v4.2s, v3.2s
        uzp2	v16.4s, v21.4s, v21.4s
        mul	v0.4s, v1.4s, v21.4s
        ldp	x5, x6, [x1, #16]
        ldp	x9, x10, [x2, #16]
        usra	v7.2d, v6.2d, #32
        umull	v1.2d, v16.2s, v3.2s
        uaddlp	v0.2d, v0.4s
        and	v2.16b, v7.16b, v19.16b
        mul	x11, x3, x7
        mul	x15, x4, x8
        umlal	v2.2d, v16.2s, v5.2s
        shl	v0.2d, v0.2d, #32
        usra	v1.2d, v7.2d, #32
        umlal	v0.2d, v4.2s, v5.2s
        umulh	x19, x3, x7
        mov	x24, v0.d[0]
        mov	x25, v0.d[1]
        usra	v1.2d, v2.2d, #32
        umulh	x23, x4, x8
        mov	x26, v1.d[0]
        mov	x27, v1.d[1]
        dup	v20.2d, x7
        xtn	v4.2s, v20.2d
        uzp2	v16.4s, v20.4s, v20.4s
        adds	x15, x15, x19
        adcs	x16, x24, x23
        ldr	q21, [x1, #32]
        ldr	q22, [x1, #48]
        uzp2	v3.4s, v21.4s, v20.4s
        xtn	v5.2s, v21.2d
        rev64	v1.4s, v21.4s
        adcs	x17, x25, x26
        adc	x19, x27, xzr
        umull	v6.2d, v4.2s, v5.2s
        umull	v7.2d, v4.2s, v3.2s
        mul	v0.4s, v1.4s, v20.4s
        usra	v7.2d, v6.2d, #32
        umull	v1.2d, v16.2s, v3.2s
        uaddlp	v0.2d, v0.4s
        and	v2.16b, v7.16b, v19.16b
        umlal	v2.2d, v16.2s, v5.2s
        shl	v0.2d, v0.2d, #32
        usra	v1.2d, v7.2d, #32
        umlal	v0.2d, v4.2s, v5.2s
        mov	x24, v0.d[0]
        mov	x25, v0.d[1]
        adds	x12, x15, x11
        adcs	x15, x16, x15
        adcs	x16, x17, x16
        adcs	x17, x19, x17
        adc	x19, xzr, x19
        adds	x13, x15, x11
        adcs	x14, x16, x12
        adcs	x15, x17, x15
        adcs	x16, x19, x16
        adcs	x17, xzr, x17
        adc	x19, xzr, x19
        usra	v1.2d, v2.2d, #32
        mov	x26, v1.d[0]
        mov	x27, v1.d[1]
        uzp2	v3.4s, v22.4s, v20.4s
        xtn	v5.2s, v22.2d
        rev64	v1.4s, v22.4s
        subs	x23, x5, x6
        cneg	x23, x23, cc  // cc = lo, ul, last
        csetm	x20, cc  // cc = lo, ul, last
        subs	x21, x10, x9
        cneg	x21, x21, cc  // cc = lo, ul, last
        mul	x22, x23, x21
        umulh	x21, x23, x21
        cinv	x20, x20, cc  // cc = lo, ul, last
        cmn	x20, #0x1
        eor	x22, x22, x20
        adcs	x16, x16, x22
        eor	x21, x21, x20
        adcs	x17, x17, x21
        adc	x19, x19, x20
        umull	v6.2d, v4.2s, v5.2s
        umull	v7.2d, v4.2s, v3.2s
        mul	v0.4s, v1.4s, v20.4s
        subs	x23, x3, x4
        cneg	x23, x23, cc  // cc = lo, ul, last
        csetm	x20, cc  // cc = lo, ul, last
        subs	x21, x8, x7
        cneg	x21, x21, cc  // cc = lo, ul, last
        mul	x22, x23, x21
        umulh	x21, x23, x21
        cinv	x20, x20, cc  // cc = lo, ul, last
        cmn	x20, #0x1
        eor	x22, x22, x20
        adcs	x12, x12, x22
        eor	x21, x21, x20
        adcs	x13, x13, x21
        adcs	x14, x14, x20
        adcs	x15, x15, x20
        adcs	x16, x16, x20
        adcs	x17, x17, x20
        adc	x19, x19, x20
        usra	v7.2d, v6.2d, #32
        umull	v24.2d, v16.2s, v3.2s
        uaddlp	v0.2d, v0.4s
        and	v2.16b, v7.16b, v19.16b
        subs	x23, x4, x6
        cneg	x23, x23, cc  // cc = lo, ul, last
        csetm	x20, cc  // cc = lo, ul, last
        subs	x21, x10, x8
        cneg	x21, x21, cc  // cc = lo, ul, last
        mul	x22, x23, x21
        umulh	x21, x23, x21
        cinv	x20, x20, cc  // cc = lo, ul, last
        cmn	x20, #0x1
        eor	x22, x22, x20
        adcs	x15, x15, x22
        eor	x21, x21, x20
        adcs	x16, x16, x21
        adcs	x17, x17, x20
        adc	x19, x19, x20
        umlal	v2.2d, v16.2s, v5.2s
        shl	v23.2d, v0.2d, #32
        usra	v24.2d, v7.2d, #32
        umlal	v23.2d, v4.2s, v5.2s
        subs	x23, x3, x5
        cneg	x23, x23, cc  // cc = lo, ul, last
        csetm	x20, cc  // cc = lo, ul, last
        subs	x21, x9, x7
        cneg	x21, x21, cc  // cc = lo, ul, last
        mul	x22, x23, x21
        umulh	x21, x23, x21
        cinv	x20, x20, cc  // cc = lo, ul, last
        cmn	x20, #0x1
        eor	x22, x22, x20
        adcs	x13, x13, x22
        eor	x21, x21, x20
        adcs	x14, x14, x21
        adcs	x15, x15, x20
        adcs	x16, x16, x20
        adcs	x17, x17, x20
        adc	x19, x19, x20
        mov	x28, v23.d[0]
        mov	x29, v23.d[1]
        usra	v24.2d, v2.2d, #32
        mov	x30, v24.d[0]
        subs	x23, x3, x6
        cneg	x23, x23, cc  // cc = lo, ul, last
        csetm	x20, cc  // cc = lo, ul, last
        subs	x21, x10, x7
        cneg	x21, x21, cc  // cc = lo, ul, last
        mul	x22, x23, x21
        umulh	x21, x23, x21
        cinv	x20, x20, cc  // cc = lo, ul, last
        cmn	x20, #0x1
        eor	x22, x22, x20
        adcs	x14, x14, x22
        eor	x21, x21, x20
        adcs	x15, x15, x21
        adcs	x16, x16, x20
        adcs	x17, x17, x20
        adc	x19, x19, x20
        ldp	x21, xzr, [x2, #32]
        dup	v20.2d, x21
        xtn	v4.2s, v20.2d
        uzp2	v16.4s, v20.4s, v20.4s
        subs	x23, x4, x5
        cneg	x23, x23, cc  // cc = lo, ul, last
        csetm	x20, cc  // cc = lo, ul, last
        subs	x21, x9, x8
        cneg	x21, x21, cc  // cc = lo, ul, last
        mul	x22, x23, x21
        umulh	x21, x23, x21
        cinv	x20, x20, cc  // cc = lo, ul, last
        cmn	x20, #0x1
        eor	x22, x22, x20
        adcs	x14, x14, x22
        eor	x21, x21, x20
        adcs	x15, x15, x21
        ldr	q21, [x1]
        ldr	q22, [x1, #16]
        adcs	x16, x16, x20
        adcs	x17, x17, x20
        adc	x19, x19, x20
        uzp2	v3.4s, v21.4s, v20.4s
        xtn	v5.2s, v21.2d
        rev64	v1.4s, v21.4s
        umull	v6.2d, v4.2s, v5.2s
        stp	x11, x12, [x0]
        stp	x13, x14, [x0, #16]
        ldp	x3, x4, [x1, #32]
        ldp	x5, x6, [x1, #48]
        ldp	x7, x8, [x2]
        ldp	x9, x10, [x2, #16]
        umull	v7.2d, v4.2s, v3.2s
        mul	v0.4s, v1.4s, v20.4s
        usra	v7.2d, v6.2d, #32
        umull	v1.2d, v16.2s, v3.2s
        adds	x12, x25, x26
        adcs	x13, x27, x28
        adc	x14, x29, x30
        uaddlp	v0.2d, v0.4s
        and	v2.16b, v7.16b, v19.16b
        umlal	v2.2d, v16.2s, v5.2s
        shl	v0.2d, v0.2d, #32
        mul	x23, x3, x8
        adds	x12, x12, x23
        mul	x23, x4, x8
        adcs	x13, x13, x23
        usra	v1.2d, v7.2d, #32
        umlal	v0.2d, v4.2s, v5.2s
        mul	x23, x5, x8
        adc	x14, x14, x23
        mov	x25, v0.d[1]
        usra	v1.2d, v2.2d, #32
        mov	x26, v1.d[0]
        umulh	x23, x3, x8
        adds	x13, x13, x23
        mov	x27, v1.d[1]
        mov	x21, v0.d[0]
        umulh	x23, x4, x8
        adc	x14, x14, x23
        mul	x23, x3, x9
        adds	x13, x13, x23
        uzp2	v3.4s, v22.4s, v20.4s
        xtn	v5.2s, v22.2d
        rev64	v1.4s, v22.4s
        umull	v6.2d, v4.2s, v5.2s
        mul	x23, x4, x9
        adc	x14, x14, x23
        umulh	x23, x3, x9
        add	x14, x14, x23
        umull	v7.2d, v4.2s, v3.2s
        mul	v0.4s, v1.4s, v20.4s
        usra	v7.2d, v6.2d, #32
        umull	v24.2d, v16.2s, v3.2s
        mul	x23, x3, x10
        add	x14, x14, x23
        adds	x15, x15, x24
        uaddlp	v0.2d, v0.4s
        and	v2.16b, v7.16b, v19.16b
        umlal	v2.2d, v16.2s, v5.2s
        shl	v23.2d, v0.2d, #32
        mov	x24, x21
        usra	v24.2d, v7.2d, #32
        umlal	v23.2d, v4.2s, v5.2s
        mov	x28, v23.d[0]
        mov	x29, v23.d[1]
        adcs	x16, x16, x12
        adcs	x17, x17, x13
        adc	x19, x19, x14
        usra	v24.2d, v2.2d, #32
        mov	x30, v24.d[0]
        ldr	q21, [x1]
        ldp	x3, x4, [x1]
        ldp	x5, x6, [x1, #16]
        ldp	x7, x8, [x2, #32]
        ldp	x9, x10, [x2, #48]
        dup	v20.2d, x9
        uzp1	v2.4s, v21.4s, v20.4s
        rev64	v1.4s, v21.4s
        adds	x12, x25, x26
        adcs	x13, x28, x27
        adc	x14, x29, x30
        uzp1	v3.4s, v20.4s, v20.4s
        mul	v0.4s, v1.4s, v20.4s
        mul	x23, x3, x8
        adds	x12, x12, x23
        uaddlp	v0.2d, v0.4s
        shl	v0.2d, v0.2d, #32
        mul	x23, x4, x8
        adcs	x13, x13, x23
        umlal	v0.2d, v3.2s, v2.2s
        mov	x26, v0.d[0]
        mov	x27, v0.d[1]
        mul	x23, x5, x8
        adc	x14, x14, x23
        umulh	x23, x3, x8
        adds	x13, x13, x23
        umulh	x23, x4, x8
        adc	x14, x14, x23
        adds	x13, x13, x26
        adc	x14, x14, x27
        umulh	x23, x3, x9
        add	x14, x14, x23
        mul	x23, x3, x10
        add	x14, x14, x23
        adds	x15, x15, x24
        adcs	x16, x16, x12
        stp	x15, x16, [x0, #32]
        adcs	x17, x17, x13
        adc	x19, x19, x14
        stp	x17, x19, [x0, #48]
        ldp	x29, x30, [sp], #16
        ldp	x27, x28, [sp], #16
        ldp	x25, x26, [sp], #16
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif

