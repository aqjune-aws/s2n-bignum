// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Multiply modulo p_25519, z := (x * y) mod p_25519
// Inputs x[4], y[4]; output z[4]
//
//    extern void bignum_mul_p25519_alt(uint64_t z[static 4],
//                                      const uint64_t x[static 4],
//                                      const uint64_t y[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = x, RDX = y
// Microsoft x64 ABI:   RCX = z, RDX = x, R8 = y
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_mul_p25519_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_mul_p25519_alt)
        .text

// These are actually right

#define z rdi
#define x rsi

// Copied in or set up

#define y rcx

// Re-use input pointers later for constant and top carry

#define d rsi
#define c rcx

#define dshort esi

// Macro for the key "multiply and add to (c,h,l)" step

#define combadd(c,h,l,numa,numb)                \
        mov     rax, numa;                      \
        mul     QWORD PTR numb;                 \
        add     l, rax;                         \
        adc     h, rdx;                         \
        adc     c, 0

// A minutely shorter form for when c = 0 initially

#define combadz(c,h,l,numa,numb)                \
        mov     rax, numa;                      \
        mul     QWORD PTR numb;                 \
        add     l, rax;                         \
        adc     h, rdx;                         \
        adc     c, c

// A short form where we don't expect a top carry

#define combads(h,l,numa,numb)                  \
        mov     rax, numa;                      \
        mul     QWORD PTR numb;                 \
        add     l, rax;                         \
        adc     h, rdx

S2N_BN_SYMBOL(bignum_mul_p25519_alt):
        _CET_ENDBR

#if WINDOWS_ABI
        push    rdi
        push    rsi
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

// Save more registers to play with

        push    r12
        push    r13
        push    r14
        push    r15

// Copy y into a safe register to start with

        mov     y, rdx

// Start the window as [r10;r9;r8] with 00 product

        mov     rax, [x]
        mul     QWORD PTR [y]
        mov     r8, rax
        mov     r9, rdx
        xor     r10, r10

// Column 1

        xor     r11, r11
        combads(r10,r9,[x],[y+8])
        combadd(r11,r10,r9,[x+8],[y])

// Column 2

        xor     r12, r12
        combadz(r12,r11,r10,[x],[y+16])
        combadd(r12,r11,r10,[x+8],[y+8])
        combadd(r12,r11,r10,[x+16],[y])

// Column 3

        xor     r13, r13
        combadz(r13,r12,r11,[x],[y+24])
        combadd(r13,r12,r11,[x+8],[y+16])
        combadd(r13,r12,r11,[x+16],[y+8])
        combadd(r13,r12,r11,[x+24],[y])

// Column 4

        xor     r14, r14
        combadz(r14,r13,r12,[x+8],[y+24])
        combadd(r14,r13,r12,[x+16],[y+16])
        combadd(r14,r13,r12,[x+24],[y+8])

// Column 5

        xor     r15, r15
        combadz(r15,r14,r13,[x+16],[y+24])
        combadd(r15,r14,r13,[x+24],[y+16])

// Final work for columns 6 and 7

        mov     rax, [x+24]
        mul     QWORD PTR [y+24]
        add     r14, rax
        adc     r15, rdx

// Now we have the full 8-digit product 2^256 * h + l where
// h = [r15,r14,r13,r12] and l = [r11,r10,r9,r8]
// and this is == 38 * h + l (mod p_25519)

        mov     dshort, 38

        mov     rax, r12
        mul     d
        add     r8, rax
        adc     r9, rdx
        sbb     c, c

        mov     rax, r13
        mul     d
        sub     rdx, c
        add     r9, rax
        adc     r10, rdx
        sbb     c, c

        mov     rax, r14
        mul     d
        sub     rdx, c
        add     r10, rax
        adc     r11, rdx
        sbb     c, c

        mov     rax, r15
        mul     d
        sub     rdx, c
        xor     c, c
        add     r11, rax
        mov     r12, rdx
        adc     r12, c

// Now we have reduced to 5 digits, 2^255 * h + l = [r12,r11,r10,r9,r8]
// Use q = h + 1 as the initial quotient estimate, either right or 1 too big.

        shld    r12, r11, 1
        lea     rax, [r12+1]
        mov     dshort, 19
        bts     r11, 63
        imul    rax, d
        add     r8, rax
        adc     r9, c
        adc     r10, c
        adc     r11, c

// Now the effective answer is 2^256 * (CF - 1) + [u3,u2,u1,u0]
// So we correct if CF = 0 by subtracting 19, either way masking to
// 255 bits, i.e. by effectively adding p_25519 to the "full" answer

        sbb     rax, rax
        not     rax
        and     rax, d
        sub     r8, rax
        sbb     r9, c
        sbb     r10, c
        sbb     r11, c
        btr     r11, 63

// Write everything back

        mov     [z], r8
        mov     [z+8], r9
        mov     [z+16], r10
        mov     [z+24], r11

// Restore registers and return

        pop     r15
        pop     r14
        pop     r13
        pop     r12

#if WINDOWS_ABI
        pop    rsi
        pop    rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
