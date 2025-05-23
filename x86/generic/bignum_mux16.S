// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Select element from 16-element table, z := xs[k*i]
// Inputs xs[16*k], i; output z[k]
//
//    extern void bignum_mux16(uint64_t k, uint64_t *z, const uint64_t *xs,
//                             uint64_t i);
//
// It is assumed that all numbers xs[16] and the target z have the same size k
// The pointer xs is to a contiguous array of size 16, elements size-k bignums
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = xs, RCX = i
// Microsoft x64 ABI:   RCX = k, RDX = z, R8 = xs, R9 = i
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_mux16)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_mux16)
        .text

#define k rdi
#define z rsi

// These get moved from original registers

#define x rcx
#define i rax

// Other registers

#define a rdx
#define b r8
#define j r9
#define n r10



S2N_BN_SYMBOL(bignum_mux16):
        _CET_ENDBR

#if WINDOWS_ABI
        push    rdi
        push    rsi
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
        mov     rcx, r9
#endif


// Copy size into decrementable counter, or skip everything if k = 0

        test    k, k
        jz      bignum_mux16_end                     // If length = 0 do nothing
        mov     n, k

// Multiply i by k so we can compare pointer offsets directly with it

        mov     rax, rcx
        mov     rcx, rdx
        mul     k

// Main loop

bignum_mux16_loop:
        mov     a, [x]
        mov     j, k
.rep 15
        mov     b, [x+8*j]
        cmp     j, i
        cmove   a, b
        add     j, k
.endr
        mov     [z], a
        add     z, 8
        add     x, 8
        dec     n
        jnz     bignum_mux16_loop

bignum_mux16_end:
#if WINDOWS_ABI
        pop    rsi
        pop    rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
