// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Negate modulo p_25519, z := (-x) mod p_25519, assuming x reduced
// Input x[4]; output z[4]
//
//    extern void bignum_neg_p25519(uint64_t z[static 4], const uint64_t x[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_neg_p25519)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_neg_p25519)
        .text

#define z rdi
#define x rsi

#define q rdx
#define n0 rax
#define n1 rcx
#define n2 r8
#define n3 r9

#define c r10

#define qshort esi

S2N_BN_SYMBOL(bignum_neg_p25519):
        _CET_ENDBR

#if WINDOWS_ABI
        push    rdi
        push    rsi
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Load the 4 digits of x and let q be an OR of all the digits

        mov     n0, [x]
        mov     q, n0
        mov     n1, [x+8]
        or      q, n1
        mov     n2, [x+16]
        or      q, n2
        mov     n3, [x+24]
        or      q, n3

// Turn q into a strict x <> 0 bitmask, and c into a masked constant [-19]
// so that [q;q;q;c] = [2^256 - 19], masked according to nonzeroness of x

        neg     q
        sbb     q, q
        mov     c, -19
        and     c, q

// Now just do [2^256 - 19] - x and then mask to 255 bits,
// which means in effect the required [2^255 - 19] - x

        sub     c, n0
        mov     [z], c
        mov     c, q
        sbb     c, n1
        mov     [z+8], c
        mov     c, q
        sbb     c, n2
        mov     [z+16], c
        sbb     q, n3
        btr     q, 63
        mov     [z+24], q

#if WINDOWS_ABI
        pop    rsi
        pop    rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
