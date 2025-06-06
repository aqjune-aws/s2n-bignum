// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Multiply by a single word modulo p_sm2, z := (c * x) mod p_sm2, assuming
// x reduced
// Inputs c, x[4]; output z[4]
//
//    extern void bignum_cmul_sm2(uint64_t z[static 4], uint64_t c,
//                                const uint64_t x[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = c, RDX = x
// Microsoft x64 ABI:   RCX = z, RDX = c, R8 = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_cmul_sm2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_cmul_sm2)
        .text

#define z rdi

// Temporarily moved here for initial multiply
#define x rcx
// Likewise this is thrown away after initial multiply
#define m rdx

#define a rax
#define c rcx

#define d0 rsi
#define d1 r8
#define d2 r9
#define d3 r10
#define h r11

// Multiplier again for second stage
#define q rdx
#define qshort edx

S2N_BN_SYMBOL(bignum_cmul_sm2):
        _CET_ENDBR

#if WINDOWS_ABI
        push    rdi
        push    rsi
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

// Shuffle inputs (since we want multiplier in rdx)

        mov     x, rdx
        mov     m, rsi

// Multiply, accumulating the result as ca = 2^256 * h + [d3;d2;d1;d0]

        mulx    d1, d0, [x]
        mulx    d2, a, [x+8]
        add     d1, a
        mulx    d3,a, [x+16]
        adc     d2, a
        mulx    h,a, [x+24]
        adc     d3, a
        adc     h, 0

// Quotient approximation is (h * (1 + 2^32 + 2^64) + d3 + 2^64) >> 64.
// Note that by hypothesis our product is <= (2^64 - 1) * (p_sm2 - 1),
// so there is no need to max this out to avoid wrapping, unlike in the
// more general case of bignum_mod_sm2.

        mov     a, d3
        mov     qshort, 1
        add     a, h
        adc     q, h

        shr     a, 32
        add     a, h

        shr     a, 32
        add     q, a

// Now compute the initial pre-reduced [h;d3;d2;d1;d0] = ca - p_sm2 * q
// = ca - (2^256 - 2^224 - 2^96 + 2^64 - 1) * q

        mov     a, q
        mov     c, q
        shl     a, 32
        shr     c, 32

        add     d3, a
        adc     h, c

        sub     a, q
        sbb     c, 0

        sub     h, q

        add     d0, q
        adc     d1, a
        adc     d2, c
        adc     d3, 0
        adc     h, 0

// Now our top word h is either zero or all 1s, and we use this to discriminate
// whether a correction is needed because our result is negative, as a bitmask
// Do a masked addition of p_sm2

        mov     a, 0xffffffff00000000
        and     a, h
        mov     c, 0xfffffffeffffffff
        and     c, h
        add     d0, h
        mov     [z], d0
        adc     d1, a
        mov     [z+8], d1
        adc     d2, h
        mov     [z+16],d2
        adc     d3, c
        mov     [z+24],d3

#if WINDOWS_ABI
        pop    rsi
        pop    rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
