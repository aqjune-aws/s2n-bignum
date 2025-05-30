// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Triple modulo p_sm2, z := (3 * x) mod p_sm2
// Input x[4]; output z[4]
//
//    extern void bignum_triple_sm2(uint64_t z[static 4], const uint64_t x[static 4]);
//
// The input x can be any 4-digit bignum, not necessarily reduced modulo p_sm2,
// and the result is always fully reduced, i.e. z = (3 * x) mod p_sm2.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_triple_sm2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_triple_sm2)
        .text

#define z rdi
#define x rsi

// Main digits of intermediate results

#define d0 r8
#define d1 r9
#define d2 r10
#define d3 r11

// Quotient estimate = top of product + 1

#define q rdx
#define h rdx
#define qshort edx

// Other temporary variables and their short version

#define a rax
#define c rcx

#define ashort eax

S2N_BN_SYMBOL(bignum_triple_sm2):
        _CET_ENDBR

#if WINDOWS_ABI
        push    rdi
        push    rsi
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// First do the multiplication by 3, getting z = [h; d3; ...; d0]
// but immediately form the quotient estimate q = h + 1

        xor     ashort, ashort

        mov     q, [x]
        mov     d0, q
        adcx    q, q
        adox    d0, q
        mov     q, [x+8]
        mov     d1, q
        adcx    q, q
        adox    d1, q
        mov     q, [x+16]
        mov     d2, q
        adcx    q, q
        adox    d2, q
        mov     q, [x+24]
        mov     d3, q
        adcx    q, q
        adox    d3, q

// For this limited range a simple quotient estimate of q = h + 1 works, where
// h = floor(z / 2^256). Then -p_sm2 <= z - q * p_sm2 < p_sm2, so we just need
// to subtract q * p_sm2 and then if that's negative, add back p_sm2.

        mov     qshort, 1
        adcx    q, a
        adox    q, a

// Now compute the initial pre-reduced [h;d3;d2;d1;d0] = z - p_sm2 * q
// = z - (2^256 - 2^224 - 2^96 + 2^64 - 1) * q

        mov     a, q
        shl     a, 32
        mov     c, a
        sub     a, q

        add     d0, q
        adc     d1, a
        adc     d2, 0
        adc     d3, c
        sbb     h, h
        not     h

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
