// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Subtract modulo m, z := (x - y) mod m, assuming x and y reduced
// Inputs x[k], y[k], m[k]; output z[k]
//
//    extern void bignum_modsub(uint64_t k, uint64_t *z, const uint64_t *x,
//                              const uint64_t *y, const uint64_t *m);
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = x, RCX = y, R8 = m
// Microsoft x64 ABI:   RCX = k, RDX = z, R8 = x, R9 = y, [RSP+40] = m
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_modsub)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_modsub)
        .text

#define k rdi
#define z rsi
#define x rdx
#define y rcx
#define m r8
#define i r9
#define j r10
#define a rax
#define c r11

S2N_BN_SYMBOL(bignum_modsub):
        _CET_ENDBR

#if WINDOWS_ABI
        push    rdi
        push    rsi
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
        mov     rcx, r9
        mov     r8, [rsp+56]
#endif

// If k = 0 do nothing

        test    k, k
        jz      bignum_modsub_end

// Subtract z := x - y and record a mask for the carry x - y < 0

        xor     c, c
        mov     j, k
        xor     i, i
bignum_modsub_subloop:
        mov     a, [x+8*i]
        sbb     a, [y+8*i]
        mov     [z+8*i], a
        inc     i
        dec     j
        jnz     bignum_modsub_subloop
        sbb     c, c

// Now do a masked addition z := z + [c] * m

        xor     i, i
bignum_modsub_addloop:
        mov     a, [m+8*i]
        and     a, c
        neg     j
        adc     [z+8*i], a
        sbb     j, j
        inc     i
        cmp     i, k
        jc      bignum_modsub_addloop

bignum_modsub_end:
#if WINDOWS_ABI
        pop    rsi
        pop    rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
