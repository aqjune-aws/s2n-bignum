// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Convert little-endian bytes to 9-digit 528-bit bignum
//
//    extern void bignum_fromlebytes_p521(uint64_t z[static 9],
//                                        const uint8_t x[static 66]);
//
// The result will be < 2^528 since it is translated from 66 bytes.
// It is mainly intended for inputs x < p_521 < 2^521 < 2^528.
//
// Since x86 is little-endian, this is just copying.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_fromlebytes_p521)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_fromlebytes_p521)
        .text

#define z rdi
#define x rsi
#define a rax

S2N_BN_SYMBOL(bignum_fromlebytes_p521):
        _CET_ENDBR

#if WINDOWS_ABI
        push    rdi
        push    rsi
        mov     rdi, rcx
        mov     rsi, rdx
#endif

        mov     a, [x]
        mov     [z], a

        mov     a, [x+8]
        mov     [z+8], a

        mov     a, [x+16]
        mov     [z+16], a

        mov     a, [x+24]
        mov     [z+24], a

        mov     a, [x+32]
        mov     [z+32], a

        mov     a, [x+40]
        mov     [z+40], a

        mov     a, [x+48]
        mov     [z+48], a

        mov     a, [x+56]
        mov     [z+56], a

        xor     eax, eax
        mov     ax, [x+64]
        mov     [z+64], a

#if WINDOWS_ABI
        pop    rsi
        pop    rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
