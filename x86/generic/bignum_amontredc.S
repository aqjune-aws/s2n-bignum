// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Almost-Montgomery reduce, z :== (x' / 2^{64p}) (congruent mod m)
// Inputs x[n], m[k], p; output z[k]
//
//    extern void bignum_amontredc(uint64_t k, uint64_t *z, uint64_t n,
//                                 const uint64_t *x, const uint64_t *m, uint64_t p);
//
// Does a :== (x' / 2^{64p}) mod m where x' = x if n <= p + k and in general
// is the lowest (p+k) digits of x. That is, p-fold almost-Montgomery reduction
// w.r.t. a k-digit modulus m giving a k-digit answer.
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = n, RCX = x, R8 = m, R9 = p
// Microsoft x64 ABI:   RCX = k, RDX = z, R8 = n, R9 = x, [RSP+40] = m, [RSP+48] = p
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_amontredc)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_amontredc)
        .text

// We copy x into r10 but it comes in in rdx originally

#define k rdi
#define z rsi
#define n r10
#define x rcx
#define m r8
#define p r9

// General temp, low part of product and mul input
#define a rax
// General temp, High part of product
#define b rdx
// Negated modular inverse
#define w QWORD PTR [rsp]
// Inner loop counter
#define j rbx
// Home for i'th digit or Montgomery multiplier
#define d rbp
#define h r11
#define e r12
#define t r13
#define i r14
#define c r15

// Some more intuitive names for temp regs in initial word-level negmodinv.

#define t1 rbx
#define t2 r14

#define ashort eax
#define cshort r15d
#define jshort ebx


S2N_BN_SYMBOL(bignum_amontredc):
        _CET_ENDBR

#if WINDOWS_ABI
        push    rdi
        push    rsi
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
        mov     rcx, r9
        mov     r8, [rsp+56]
        mov     r9, [rsp+64]
#endif

// Save registers and allocate space on stack for non-register variable w

        push    rbx
        push    rbp
        push    r12
        push    r13
        push    r14
        push    r15
        sub     rsp, 8

// If k = 0 the whole operation is trivial

        test    k, k
        jz      bignum_amontredc_end

// Move n input into its permanent home, since we need rdx for multiplications

        mov     n, rdx

// Compute word-level negated modular inverse w for m == m[0].

        mov     a, [m]

        mov     t2, a
        mov     t1, a
        shl     t2, 2
        sub     t1, t2
        xor     t1, 2

        mov     t2, t1
        imul    t2, a
        mov     ashort, 2
        add     a, t2
        add     t2, 1

        imul    t1, a

        imul    t2, t2
        mov     ashort, 1
        add     a, t2
        imul    t1, a

        imul    t2, t2
        mov     ashort, 1
        add     a, t2
        imul    t1, a

        imul    t2, t2
        mov     ashort, 1
        add     a, t2
        imul    t1, a

        mov     w, t1

// Initialize z to the lowest k digits of the input, zero-padding if n < k.

        mov     j, k
        cmp     n, k
        cmovc   j, n
        xor     i, i
        test    j, j
        jz      bignum_amontredc_padloop
bignum_amontredc_copyloop:
        mov     a, [x+8*i]
        mov     [z+8*i], a
        inc     i
        cmp     i, j
        jc      bignum_amontredc_copyloop

        cmp     i, k
        jnc     bignum_amontredc_initialized

        xor     j, j
bignum_amontredc_padloop:
        mov     [z+8*i], j
        inc     i
        cmp     i, k
        jc      bignum_amontredc_padloop

bignum_amontredc_initialized:
        xor     c, c

// Now if p = 0 that's the end of the operation

        test    p, p
        jz      bignum_amontredc_end

// Outer loop, just doing a standard Montgomery reduction on z

        xor     i, i
bignum_amontredc_outerloop:
        mov     e, [z]
        mov     d, w
        imul    d, e
        mov     a, [m]
        mul     d
        add     a, e            // Will be zero but want the carry
        mov     h, rdx
        mov     jshort, 1
        mov     t, k
        dec     t
        jz      bignum_amontredc_montend

bignum_amontredc_montloop:
        adc     h, [z+8*j]
        sbb     e, e
        mov     a, [m+8*j]
        mul     d
        sub     rdx, e
        add     a, h
        mov     [z+8*j-8], a
        mov     h, rdx
        inc     j
        dec     t
        jnz     bignum_amontredc_montloop

bignum_amontredc_montend:
        adc     h, c
        mov     cshort, 0
        adc     c, 0

        add     j, i
        cmp     j, n
        jnc     bignum_amontredc_offtheend
        mov     a, [x+8*j]
        add     h, a
        adc     c, 0
bignum_amontredc_offtheend:
        mov     [z+8*k-8], h

// End of outer loop.

        inc     i
        cmp     i, p
        jc      bignum_amontredc_outerloop

// Now convert carry word, which is always in {0,1}, into a mask "d"
// and do a masked subtraction of m for the final almost-Montgomery result.

        xor     d, d
        sub     d, c
        xor     e, e
        xor     j, j
bignum_amontredc_corrloop:
        mov     a, [m+8*j]
        and     a, d
        neg     e
        sbb     [z+8*j], a
        sbb     e, e
        inc     j
        cmp     j, k
        jc      bignum_amontredc_corrloop

bignum_amontredc_end:
        add     rsp, 8
        pop     r15
        pop     r14
        pop     r13
        pop     r12
        pop     rbp
        pop     rbx

#if WINDOWS_ABI
        pop    rsi
        pop    rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
