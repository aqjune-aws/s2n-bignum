// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Montgomery multiply, z := (x * y / 2^256) mod p_256k1
// Inputs x[4], y[4]; output z[4]
//
//    extern void bignum_montmul_p256k1_alt(uint64_t z[static 4],
//                                          const uint64_t x[static 4],
//                                          const uint64_t y[static 4]);
//
// Does z := (2^{-256} * x * y) mod p_256k1, assuming that the inputs x and y
// satisfy x * y <= 2^256 * p_256k2 (in particular this is true if we are in
// the "usual" case x < p_256k1 and y < p_256k1).
//
// Standard x86-64 ABI: RDI = z, RSI = x, RDX = y
// Microsoft x64 ABI:   RCX = z, RDX = x, R8 = y
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_montmul_p256k1_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_montmul_p256k1_alt)
        .text

// These are actually right

#define z rdi
#define x rsi

// Copied in or set up

#define y rcx

// Re-used for constants in second part

#define w rsi

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

S2N_BN_SYMBOL(bignum_montmul_p256k1_alt):
        _CET_ENDBR

#if WINDOWS_ABI
        push    rdi
        push    rsi
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

// Save more registers to play with

        push    rbx
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
        combadz(r11,r10,r9,[x+8],[y])

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
// Do Montgomery reductions, now using rcx as a carry-saver.

        mov     w, 0xd838091dd2253531
        mov     rbx, 4294968273

// Montgomery reduce row 0

        mov     rax, rbx
        imul    r8, w
        mul     r8
        sub     r9, rdx
        sbb     rcx, rcx

// Montgomery reduce row 1

        mov     rax, rbx
        imul    r9, w
        mul     r9
        neg     rcx
        sbb     r10, rdx
        sbb     rcx, rcx

// Montgomery reduce row 2

        mov     rax, rbx
        imul    r10, w
        mul     r10
        neg     rcx
        sbb     r11, rdx
        sbb     rcx, rcx

// Montgomery reduce row 3

        mov     rax, rbx
        imul    r11, w
        mul     r11
        neg     rcx

// Now [r15,r14,r13,r12] := [r15,r14,r13,r12] + [r11,r10,r9,r8] - (rdx + CF)

        sbb     r8, rdx
        sbb     r9, 0
        sbb     r10, 0
        sbb     r11, 0

        add     r12, r8
        adc     r13, r9
        adc     r14, r10
        adc     r15, r11
        sbb     w, w

// Let b be the top carry captured just above as w = (2^64-1) * b
// Now if [b,r15,r14,r13,r12] >= p_256k1, subtract p_256k1, i.e. add 4294968273
// and either way throw away the top word. [b,r15,r14,r13,r12] - p_256k1 =
// [(b - 1),r15,r14,r13,r12] + 4294968273. If [r15,r14,r13,r12] + 4294968273
// gives carry flag CF then >= comparison is top = 0 <=> b - 1 + CF = 0 which
// is equivalent to b \/ CF, and so to (2^64-1) * b + (2^64 - 1) + CF >= 2^64

        mov     r8, r12
        add     r8, rbx
        mov     r9, r13
        adc     r9, 0
        mov     r10, r14
        adc     r10, 0
        mov     r11, r15
        adc     r11, 0

        adc     w, -1

// Write everything back

        cmovc   r12, r8
        mov     [z], r12
        cmovc   r13, r9
        mov     [z+8], r13
        cmovc   r14, r10
        mov     [z+16], r14
        cmovc   r15, r11
        mov     [z+24], r15

// Restore registers and return

        pop     r15
        pop     r14
        pop     r13
        pop     r12
        pop     rbx

#if WINDOWS_ABI
        pop    rsi
        pop    rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
