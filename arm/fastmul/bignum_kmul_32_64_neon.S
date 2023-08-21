// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// ----------------------------------------------------------------------------
// Multiply z := x * y
// Inputs x[32], y[32]; output z[64]; temporary buffer t[>=96]
//
//    extern void bignum_kmul_32_64_neon
//     (uint64_t z[static 64], uint64_t x[static 32], uint64_t y[static 32],
//      uint64_t t[static 96])
//
// This is a Karatsuba-style function multiplying half-sized results
// internally and using temporary buffer t for intermediate results.
//
// Standard ARM ABI: X0 = z, X1 = x, X2 = y, X3 = t
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_kmul_32_64_neon)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_kmul_32_64_neon)
        .text
        .balign 4

#define K 16
#define L 8 // this is (K/2)

#define z x19
#define x x20
#define y x21
#define t x22

#define c x16

S2N_BN_SYMBOL(bignum_kmul_32_64_neon):

// Save extra registers and return address, store parameters safely

        sub sp, sp, #96
        stp     x19, x20, [sp, #80]
        stp     x21, x22, [sp, #64]
        stp     x23, x24, [sp, #48]
        stp     x25, x26, [sp, #32]
        stp     x27, x28, [sp, #16]
        stp     x29, x30, [sp]

        mov     z, x0
        mov     x, x1
        mov     y, x2
        mov     t, x3

// Compute L = x_lo * y_lo in bottom half of buffer (size 16 x 16 -> 32)

        bl      bignum_kmul_32_64_neon_local_kmul_16_32

// Compute H = x_hi * y_hi in top half of buffer (size 16 x 16 -> 32)

        add     x0, z, #16*K
        add     x1, x, #8*K
        add     x2, y, #8*K
        mov     x3, t
        bl      bignum_kmul_32_64_neon_local_kmul_16_32

// Compute absolute difference [t..] = |x_lo - x_hi|
// and the sign x = sgn(x_lo - x_hi) as a bitmask (all 1s for negative)
// Note that we overwrite the pointer x itself with this sign,
// which is safe since we no longer need it.

        ldp     x0, x1, [x, #128]
        ldp     x16, x17, [x]
        subs    x0, x0, x16
        sbcs    x1, x1, x17

        ldp     x2, x3, [x, #144]
        ldp     x16, x17, [x, #16]
        sbcs    x2, x2, x16
        sbcs    x3, x3, x17

        ldp     x4, x5, [x, #160]
        ldp     x16, x17, [x, #32]
        sbcs    x4, x4, x16
        sbcs    x5, x5, x17

        ldp     x6, x7, [x, #176]
        ldp     x16, x17, [x, #48]
        sbcs    x6, x6, x16
        sbcs    x7, x7, x17

        ldp     x8, x9, [x, #192]
        ldp     x16, x17, [x, #64]
        sbcs    x8, x8, x16
        sbcs    x9, x9, x17

        ldp     x10, x11, [x, #208]
        ldp     x16, x17, [x, #80]
        sbcs    x10, x10, x16
        sbcs    x11, x11, x17

        ldp     x12, x13, [x, #224]
        ldp     x16, x17, [x, #96]
        sbcs    x12, x12, x16
        sbcs    x13, x13, x17

        ldp     x14, x15, [x, #240]
        ldp     x16, x17, [x, #112]
        sbcs    x14, x14, x16
        sbcs    x15, x15, x17

        sbc     x, xzr, xzr

        adds    xzr, x, x

        eor     x0, x0, x
        adcs    x0, x0, xzr
        eor     x1, x1, x
        adcs    x1, x1, xzr
        stp     x0, x1, [t]

        eor     x2, x2, x
        adcs    x2, x2, xzr
        eor     x3, x3, x
        adcs    x3, x3, xzr
        stp     x2, x3, [t, #16]

        eor     x4, x4, x
        adcs    x4, x4, xzr
        eor     x5, x5, x
        adcs    x5, x5, xzr
        stp     x4, x5, [t, #32]

        eor     x6, x6, x
        adcs    x6, x6, xzr
        eor     x7, x7, x
        adcs    x7, x7, xzr
        stp     x6, x7, [t, #48]

        eor     x8, x8, x
        adcs    x8, x8, xzr
        eor     x9, x9, x
        adcs    x9, x9, xzr
        stp     x8, x9, [t, #64]

        eor     x10, x10, x
        adcs    x10, x10, xzr
        eor     x11, x11, x
        adcs    x11, x11, xzr
        stp     x10, x11, [t, #80]

        eor     x12, x12, x
        adcs    x12, x12, xzr
        eor     x13, x13, x
        adcs    x13, x13, xzr
        stp     x12, x13, [t, #96]

        eor     x14, x14, x
        adcs    x14, x14, xzr
        eor     x15, x15, x
        adc     x15, x15, xzr
        stp     x14, x15, [t, #112]

// Compute the other absolute difference [t+8*K..] = |y_hi - y_lo|
// Collect the combined product sign bitmask (all 1s for negative) as
// y = sgn((x_lo - x_hi) * (y_hi - y_lo)), overwriting the y pointer.

        ldp     x0, x1, [y]
        ldp     x16, x17, [y, #128]
        subs    x0, x0, x16
        sbcs    x1, x1, x17

        ldp     x2, x3, [y, #16]
        ldp     x16, x17, [y, #144]
        sbcs    x2, x2, x16
        sbcs    x3, x3, x17

        ldp     x4, x5, [y, #32]
        ldp     x16, x17, [y, #160]
        sbcs    x4, x4, x16
        sbcs    x5, x5, x17

        ldp     x6, x7, [y, #48]
        ldp     x16, x17, [y, #176]
        sbcs    x6, x6, x16
        sbcs    x7, x7, x17

        ldp     x8, x9, [y, #64]
        ldp     x16, x17, [y, #192]
        sbcs    x8, x8, x16
        sbcs    x9, x9, x17

        ldp     x10, x11, [y, #80]
        ldp     x16, x17, [y, #208]
        sbcs    x10, x10, x16
        sbcs    x11, x11, x17

        ldp     x12, x13, [y, #96]
        ldp     x16, x17, [y, #224]
        sbcs    x12, x12, x16
        sbcs    x13, x13, x17

        ldp     x14, x15, [y, #112]
        ldp     x16, x17, [y, #240]
        sbcs    x14, x14, x16
        sbcs    x15, x15, x17

        sbc     y, xzr, xzr

        adds    xzr, y, y

        eor     x0, x0, y
        adcs    x0, x0, xzr
        eor     x1, x1, y
        adcs    x1, x1, xzr
        stp     x0, x1, [t, #128]

        eor     x2, x2, y
        adcs    x2, x2, xzr
        eor     x3, x3, y
        adcs    x3, x3, xzr
        stp     x2, x3, [t, #128+16]

        eor     x4, x4, y
        adcs    x4, x4, xzr
        eor     x5, x5, y
        adcs    x5, x5, xzr
        stp     x4, x5, [t, #128+32]

        eor     x6, x6, y
        adcs    x6, x6, xzr
        eor     x7, x7, y
        adcs    x7, x7, xzr
        stp     x6, x7, [t, #128+48]

        eor     x8, x8, y
        adcs    x8, x8, xzr
        eor     x9, x9, y
        adcs    x9, x9, xzr
        stp     x8, x9, [t, #128+64]

        eor     x10, x10, y
        adcs    x10, x10, xzr
        eor     x11, x11, y
        adcs    x11, x11, xzr
        stp     x10, x11, [t, #128+80]

        eor     x12, x12, y
        adcs    x12, x12, xzr
        eor     x13, x13, y
        adcs    x13, x13, xzr
        stp     x12, x13, [t, #128+96]

        eor     x14, x14, y
        adcs    x14, x14, xzr
        eor     x15, x15, y
        adc     x15, x15, xzr
        stp     x14, x15, [t, #128+112]

        eor     y, y, x

// Compute H' = H + L_top in place of H (it cannot overflow)

        ldp     x0, x1, [z, #16*16]
        ldp     x2, x3, [z, #16*L]
        adds    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*16]

        ldp     x0, x1, [z, #16*17]
        ldp     x2, x3, [z, #16*9]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*17]

        ldp     x0, x1, [z, #16*18]
        ldp     x2, x3, [z, #16*10]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*18]

        ldp     x0, x1, [z, #16*19]
        ldp     x2, x3, [z, #16*11]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*19]

        ldp     x0, x1, [z, #16*20]
        ldp     x2, x3, [z, #16*12]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*20]

        ldp     x0, x1, [z, #16*21]
        ldp     x2, x3, [z, #16*13]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*21]

        ldp     x0, x1, [z, #16*22]
        ldp     x2, x3, [z, #16*14]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*22]

        ldp     x0, x1, [z, #16*23]
        ldp     x2, x3, [z, #16*15]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*23]

        ldp     x0, x1, [z, #16*24]
        adcs    x0, x0, xzr
        adcs    x1, x1, xzr
        stp     x0, x1, [z, #16*24]

        ldp     x0, x1, [z, #16*25]
        adcs    x0, x0, xzr
        adcs    x1, x1, xzr
        stp     x0, x1, [z, #16*25]

        ldp     x0, x1, [z, #16*26]
        adcs    x0, x0, xzr
        adcs    x1, x1, xzr
        stp     x0, x1, [z, #16*26]

        ldp     x0, x1, [z, #16*27]
        adcs    x0, x0, xzr
        adcs    x1, x1, xzr
        stp     x0, x1, [z, #16*27]

        ldp     x0, x1, [z, #16*28]
        adcs    x0, x0, xzr
        adcs    x1, x1, xzr
        stp     x0, x1, [z, #16*28]

        ldp     x0, x1, [z, #16*29]
        adcs    x0, x0, xzr
        adcs    x1, x1, xzr
        stp     x0, x1, [z, #16*29]

        ldp     x0, x1, [z, #16*30]
        adcs    x0, x0, xzr
        adcs    x1, x1, xzr
        stp     x0, x1, [z, #16*30]

        ldp     x0, x1, [z, #16*31]
        adcs    x0, x0, xzr
        adc     x1, x1, xzr
        stp     x0, x1, [z, #16*31]

// Compute M = |x_lo - x_hi| * |y_hi - y_lo|, size 32

        add     x0, t, #16*K
        mov     x1, t
        add     x2, t, #8*K
        add     x3, t, #32*K
        bl      bignum_kmul_32_64_neon_local_kmul_16_32

// Add the interlocking H' and L_bot terms
// Intercept the carry at the 3k position and store it in x.
// Again, we no longer need the input x was pointing at.

        ldp     x0, x1, [z, #16*16]
        ldp     x2, x3, [z]
        adds    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*8]

        ldp     x0, x1, [z, #16*17]
        ldp     x2, x3, [z, #16*1]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*9]

        ldp     x0, x1, [z, #16*18]
        ldp     x2, x3, [z, #16*2]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*10]

        ldp     x0, x1, [z, #16*19]
        ldp     x2, x3, [z, #16*3]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*11]

        ldp     x0, x1, [z, #16*20]
        ldp     x2, x3, [z, #16*4]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*12]

        ldp     x0, x1, [z, #16*21]
        ldp     x2, x3, [z, #16*5]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*13]

        ldp     x0, x1, [z, #16*22]
        ldp     x2, x3, [z, #16*6]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*14]

        ldp     x0, x1, [z, #16*23]
        ldp     x2, x3, [z, #16*7]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*15]

        ldp     x0, x1, [z, #16*16]
        ldp     x2, x3, [z, #16*24]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*16]

        ldp     x0, x1, [z, #16*17]
        ldp     x2, x3, [z, #16*25]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*17]

        ldp     x0, x1, [z, #16*18]
        ldp     x2, x3, [z, #16*26]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*18]

        ldp     x0, x1, [z, #16*19]
        ldp     x2, x3, [z, #16*27]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*19]

        ldp     x0, x1, [z, #16*20]
        ldp     x2, x3, [z, #16*28]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*20]

        ldp     x0, x1, [z, #16*21]
        ldp     x2, x3, [z, #16*29]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*21]

        ldp     x0, x1, [z, #16*22]
        ldp     x2, x3, [z, #16*30]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*22]

        ldp     x0, x1, [z, #16*23]
        ldp     x2, x3, [z, #16*31]
        adcs    x0, x0, x2
        adcs    x1, x1, x3
        stp     x0, x1, [z, #16*23]

        cset      x, cs

// Add the sign-adjusted mid-term cross product M

        cmn     y, y

        ldp     x0, x1, [z, #128]
        ldp     x2, x3, [t, #128+128]
        eor     x2, x2, y
        adcs    x0, x0, x2
        eor     x3, x3, y
        adcs    x1, x1, x3
        stp     x0, x1, [z, #128]

        ldp     x0, x1, [z, #144]
        ldp     x2, x3, [t, #128+144]
        eor     x2, x2, y
        adcs    x0, x0, x2
        eor     x3, x3, y
        adcs    x1, x1, x3
        stp     x0, x1, [z, #144]

        ldp     x0, x1, [z, #160]
        ldp     x2, x3, [t, #128+160]
        eor     x2, x2, y
        adcs    x0, x0, x2
        eor     x3, x3, y
        adcs    x1, x1, x3
        stp     x0, x1, [z, #160]

        ldp     x0, x1, [z, #176]
        ldp     x2, x3, [t, #128+176]
        eor     x2, x2, y
        adcs    x0, x0, x2
        eor     x3, x3, y
        adcs    x1, x1, x3
        stp     x0, x1, [z, #176]

        ldp     x0, x1, [z, #192]
        ldp     x2, x3, [t, #128+192]
        eor     x2, x2, y
        adcs    x0, x0, x2
        eor     x3, x3, y
        adcs    x1, x1, x3
        stp     x0, x1, [z, #192]

        ldp     x0, x1, [z, #208]
        ldp     x2, x3, [t, #128+208]
        eor     x2, x2, y
        adcs    x0, x0, x2
        eor     x3, x3, y
        adcs    x1, x1, x3
        stp     x0, x1, [z, #208]

        ldp     x0, x1, [z, #224]
        ldp     x2, x3, [t, #128+224]
        eor     x2, x2, y
        adcs    x0, x0, x2
        eor     x3, x3, y
        adcs    x1, x1, x3
        stp     x0, x1, [z, #224]

        ldp     x0, x1, [z, #240]
        ldp     x2, x3, [t, #128+240]
        eor     x2, x2, y
        adcs    x0, x0, x2
        eor     x3, x3, y
        adcs    x1, x1, x3
        stp     x0, x1, [z, #240]

        ldp     x0, x1, [z, #256]
        ldp     x2, x3, [t, #128+256]
        eor     x2, x2, y
        adcs    x0, x0, x2
        eor     x3, x3, y
        adcs    x1, x1, x3
        stp     x0, x1, [z, #256]

        ldp     x0, x1, [z, #272]
        ldp     x2, x3, [t, #128+272]
        eor     x2, x2, y
        adcs    x0, x0, x2
        eor     x3, x3, y
        adcs    x1, x1, x3
        stp     x0, x1, [z, #272]

        ldp     x0, x1, [z, #288]
        ldp     x2, x3, [t, #128+288]
        eor     x2, x2, y
        adcs    x0, x0, x2
        eor     x3, x3, y
        adcs    x1, x1, x3
        stp     x0, x1, [z, #288]

        ldp     x0, x1, [z, #304]
        ldp     x2, x3, [t, #128+304]
        eor     x2, x2, y
        adcs    x0, x0, x2
        eor     x3, x3, y
        adcs    x1, x1, x3
        stp     x0, x1, [z, #304]

        ldp     x0, x1, [z, #320]
        ldp     x2, x3, [t, #128+320]
        eor     x2, x2, y
        adcs    x0, x0, x2
        eor     x3, x3, y
        adcs    x1, x1, x3
        stp     x0, x1, [z, #320]

        ldp     x0, x1, [z, #336]
        ldp     x2, x3, [t, #128+336]
        eor     x2, x2, y
        adcs    x0, x0, x2
        eor     x3, x3, y
        adcs    x1, x1, x3
        stp     x0, x1, [z, #336]

        ldp     x0, x1, [z, #352]
        ldp     x2, x3, [t, #128+352]
        eor     x2, x2, y
        adcs    x0, x0, x2
        eor     x3, x3, y
        adcs    x1, x1, x3
        stp     x0, x1, [z, #352]

        ldp     x0, x1, [z, #368]
        ldp     x2, x3, [t, #128+368]
        eor     x2, x2, y
        adcs    x0, x0, x2
        eor     x3, x3, y
        adcs    x1, x1, x3
        stp     x0, x1, [z, #368]

// Get the next digits effectively resulting so far starting at 3k
// [...,c,c,c,c,x]

        adcs    x, y, x
        adc     c, y, xzr

// Now propagate through the top quarter of the result

        ldp     x0, x1, [z, #16*24]
        adds    x0, x0, x
        adcs    x1, x1, c
        stp     x0, x1, [z, #16*24]

        ldp     x0, x1, [z, #16*25]
        adcs    x0, x0, c
        adcs    x1, x1, c
        stp     x0, x1, [z, #16*25]

        ldp     x0, x1, [z, #16*26]
        adcs    x0, x0, c
        adcs    x1, x1, c
        stp     x0, x1, [z, #16*26]

        ldp     x0, x1, [z, #16*27]
        adcs    x0, x0, c
        adcs    x1, x1, c
        stp     x0, x1, [z, #16*27]

        ldp     x0, x1, [z, #16*28]
        adcs    x0, x0, c
        adcs    x1, x1, c
        stp     x0, x1, [z, #16*28]

        ldp     x0, x1, [z, #16*29]
        adcs    x0, x0, c
        adcs    x1, x1, c
        stp     x0, x1, [z, #16*29]

        ldp     x0, x1, [z, #16*30]
        adcs    x0, x0, c
        adcs    x1, x1, c
        stp     x0, x1, [z, #16*30]

        ldp     x0, x1, [z, #16*31]
        adcs    x0, x0, c
        adc     x1, x1, c
        stp     x0, x1, [z, #16*31]

// Restore and return

        ldp     x29, x30, [sp]
        ldp     x27, x28, [sp, #16]
        ldp     x25, x26, [sp, #32]
        ldp     x23, x24, [sp, #48]
        ldp     x21, x22, [sp, #64]
        ldp     x19, x20, [sp, #80]
        add sp, sp, #96
        ret

// Local copy of bignum_kmul_16_32_neon, identical to main one except that it
// only preserves the key registers we need to be stable in the main code.
// This includes in turn a copy of bignum_mul_8_16_neon.

bignum_kmul_32_64_neon_local_kmul_16_32:
        sub sp, sp, #48
        stp     x19, x20, [sp, #32]
        stp     x21, x22, [sp, #16]
        stp     x23, x30, [sp]
        mov     x25, x0
        mov     x26, x1
        mov     x27, x2
        mov     x28, x3
        bl      bignum_kmul_32_64_neon_local_mul_8_16
        ldp     x10, x11, [x26]
        ldp     x8, x9, [x26, #64]
        subs    x10, x10, x8
        sbcs    x11, x11, x9
        ldp     x12, x13, [x26, #16]
        ldp     x8, x9, [x26, #80]
        sbcs    x12, x12, x8
        sbcs    x13, x13, x9
        ldp     x14, x15, [x26, #32]
        ldp     x8, x9, [x26, #96]
        sbcs    x14, x14, x8
        sbcs    x15, x15, x9
        ldp     x16, x17, [x26, #48]
        ldp     x8, x9, [x26, #112]
        sbcs    x16, x16, x8
        sbcs    x17, x17, x9
        csetm   x29, cc
        cmn     x29, x29
        eor     x10, x10, x29
        adcs    x10, x10, xzr
        eor     x11, x11, x29
        adcs    x11, x11, xzr
        stp     x10, x11, [x28]
        eor     x12, x12, x29
        adcs    x12, x12, xzr
        eor     x13, x13, x29
        adcs    x13, x13, xzr
        stp     x12, x13, [x28, #16]
        eor     x14, x14, x29
        adcs    x14, x14, xzr
        eor     x15, x15, x29
        adcs    x15, x15, xzr
        stp     x14, x15, [x28, #32]
        eor     x16, x16, x29
        adcs    x16, x16, xzr
        eor     x17, x17, x29
        adcs    x17, x17, xzr
        stp     x16, x17, [x28, #48]
        add     x0, x25, #0x80
        add     x1, x26, #0x40
        add     x2, x27, #0x40
        bl      bignum_kmul_32_64_neon_local_mul_8_16
        ldp     x10, x11, [x27]
        ldp     x8, x9, [x27, #64]
        subs    x10, x8, x10
        sbcs    x11, x9, x11
        ldp     x12, x13, [x27, #16]
        ldp     x8, x9, [x27, #80]
        sbcs    x12, x8, x12
        sbcs    x13, x9, x13
        ldp     x14, x15, [x27, #32]
        ldp     x8, x9, [x27, #96]
        sbcs    x14, x8, x14
        sbcs    x15, x9, x15
        ldp     x16, x17, [x27, #48]
        ldp     x8, x9, [x27, #112]
        sbcs    x16, x8, x16
        sbcs    x17, x9, x17
        csetm   x19, cc
        cmn     x19, x19
        eor     x10, x10, x19
        adcs    x10, x10, xzr
        eor     x11, x11, x19
        adcs    x11, x11, xzr
        stp     x10, x11, [x28, #64]
        eor     x12, x12, x19
        adcs    x12, x12, xzr
        eor     x13, x13, x19
        adcs    x13, x13, xzr
        stp     x12, x13, [x28, #80]
        eor     x14, x14, x19
        adcs    x14, x14, xzr
        eor     x15, x15, x19
        adcs    x15, x15, xzr
        stp     x14, x15, [x28, #96]
        eor     x16, x16, x19
        adcs    x16, x16, xzr
        eor     x17, x17, x19
        adcs    x17, x17, xzr
        stp     x16, x17, [x28, #112]
        eor     x29, x29, x19
        ldp     x10, x11, [x25, #128]
        ldp     x12, x13, [x25, #64]
        adds    x10, x10, x12
        adcs    x11, x11, x13
        stp     x10, x11, [x25, #128]
        ldp     x10, x11, [x25, #144]
        ldp     x12, x13, [x25, #80]
        adcs    x10, x10, x12
        adcs    x11, x11, x13
        stp     x10, x11, [x25, #144]
        ldp     x10, x11, [x25, #160]
        ldp     x12, x13, [x25, #96]
        adcs    x10, x10, x12
        adcs    x11, x11, x13
        stp     x10, x11, [x25, #160]
        ldp     x10, x11, [x25, #176]
        ldp     x12, x13, [x25, #112]
        adcs    x10, x10, x12
        adcs    x11, x11, x13
        stp     x10, x11, [x25, #176]
        ldp     x10, x11, [x25, #192]
        adcs    x10, x10, xzr
        adcs    x11, x11, xzr
        stp     x10, x11, [x25, #192]
        ldp     x10, x11, [x25, #208]
        adcs    x10, x10, xzr
        adcs    x11, x11, xzr
        stp     x10, x11, [x25, #208]
        ldp     x10, x11, [x25, #224]
        adcs    x10, x10, xzr
        adcs    x11, x11, xzr
        stp     x10, x11, [x25, #224]
        ldp     x10, x11, [x25, #240]
        adcs    x10, x10, xzr
        adcs    x11, x11, xzr
        stp     x10, x11, [x25, #240]
        add     x0, x28, #0x80
        mov     x1, x28
        add     x2, x28, #0x40
        bl      bignum_kmul_32_64_neon_local_mul_8_16
        ldp     x0, x1, [x25]
        ldp     x16, x17, [x25, #128]
        adds    x0, x0, x16
        adcs    x1, x1, x17
        ldp     x2, x3, [x25, #16]
        ldp     x16, x17, [x25, #144]
        adcs    x2, x2, x16
        adcs    x3, x3, x17
        ldp     x4, x5, [x25, #32]
        ldp     x16, x17, [x25, #160]
        adcs    x4, x4, x16
        adcs    x5, x5, x17
        ldp     x6, x7, [x25, #48]
        ldp     x16, x17, [x25, #176]
        adcs    x6, x6, x16
        adcs    x7, x7, x17
        ldp     x8, x9, [x25, #128]
        ldp     x16, x17, [x25, #192]
        adcs    x8, x8, x16
        adcs    x9, x9, x17
        ldp     x10, x11, [x25, #144]
        ldp     x16, x17, [x25, #208]
        adcs    x10, x10, x16
        adcs    x11, x11, x17
        ldp     x12, x13, [x25, #160]
        ldp     x16, x17, [x25, #224]
        adcs    x12, x12, x16
        adcs    x13, x13, x17
        ldp     x14, x15, [x25, #176]
        ldp     x16, x17, [x25, #240]
        adcs    x14, x14, x16
        adcs    x15, x15, x17
        cset    x26, cs
        cmn     x29, x29
        ldp     x16, x17, [x28, #128]
        eor     x16, x16, x29
        adcs    x0, x0, x16
        eor     x17, x17, x29
        adcs    x1, x1, x17
        stp     x0, x1, [x25, #64]
        ldp     x16, x17, [x28, #144]
        eor     x16, x16, x29
        adcs    x2, x2, x16
        eor     x17, x17, x29
        adcs    x3, x3, x17
        stp     x2, x3, [x25, #80]
        ldp     x16, x17, [x28, #160]
        eor     x16, x16, x29
        adcs    x4, x4, x16
        eor     x17, x17, x29
        adcs    x5, x5, x17
        stp     x4, x5, [x25, #96]
        ldp     x16, x17, [x28, #176]
        eor     x16, x16, x29
        adcs    x6, x6, x16
        eor     x17, x17, x29
        adcs    x7, x7, x17
        stp     x6, x7, [x25, #112]
        ldp     x16, x17, [x28, #192]
        eor     x16, x16, x29
        adcs    x8, x8, x16
        eor     x17, x17, x29
        adcs    x9, x9, x17
        stp     x8, x9, [x25, #128]
        ldp     x16, x17, [x28, #208]
        eor     x16, x16, x29
        adcs    x10, x10, x16
        eor     x17, x17, x29
        adcs    x11, x11, x17
        stp     x10, x11, [x25, #144]
        ldp     x16, x17, [x28, #224]
        eor     x16, x16, x29
        adcs    x12, x12, x16
        eor     x17, x17, x29
        adcs    x13, x13, x17
        stp     x12, x13, [x25, #160]
        ldp     x16, x17, [x28, #240]
        eor     x16, x16, x29
        adcs    x14, x14, x16
        eor     x17, x17, x29
        adcs    x15, x15, x17
        stp     x14, x15, [x25, #176]
        adcs    x27, x29, x26
        adc     x28, x29, xzr
        ldp     x10, x11, [x25, #192]
        adds    x10, x10, x27
        adcs    x11, x11, x28
        stp     x10, x11, [x25, #192]
        ldp     x10, x11, [x25, #208]
        adcs    x10, x10, x28
        adcs    x11, x11, x28
        stp     x10, x11, [x25, #208]
        ldp     x10, x11, [x25, #224]
        adcs    x10, x10, x28
        adcs    x11, x11, x28
        stp     x10, x11, [x25, #224]
        ldp     x10, x11, [x25, #240]
        adcs    x10, x10, x28
        adcs    x11, x11, x28
        stp     x10, x11, [x25, #240]
        ldp     x23, x30, [sp]
        ldp     x21, x22, [sp, #16]
        ldp     x19, x20, [sp, #32]
        add sp, sp, #48
        ret

bignum_kmul_32_64_neon_local_mul_8_16:
        sub sp, sp, #48
        stp	x25, x26, [sp, #32]
        stp	x27, x28, [sp, #16]
        stp	x29, x30, [sp]
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
        ldp	x29, x30, [sp]
        ldp	x27, x28, [sp, #16]
        ldp	x25, x26, [sp, #32]
        add sp, sp, #48
        ret


#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif

