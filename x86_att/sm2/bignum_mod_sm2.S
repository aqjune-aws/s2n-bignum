// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Reduce modulo field characteristic, z := x mod p_sm2
// Input x[k]; output z[4]
//
//    extern void bignum_mod_sm2(uint64_t z[static 4], uint64_t k, const uint64_t *x);
//
// Standard x86-64 ABI: RDI = z, RSI = k, RDX = x
// Microsoft x64 ABI:   RCX = z, RDX = k, R8 = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_mod_sm2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_mod_sm2)
        .text

#define z %rdi
#define k %rsi
#define x %rdx

#define m0 %r8
#define m1 %r9
#define m2 %r10
#define m3 %r11
#define d %r12

#define n0 %rax
#define n1 %rbx
#define n3 %rcx
#define q %rcx

#define qshort %ecx

S2N_BN_SYMBOL(bignum_mod_sm2):
        _CET_ENDBR

#if WINDOWS_ABI
        pushq   %rdi
        pushq   %rsi
        movq    %rcx, %rdi
        movq    %rdx, %rsi
        movq    %r8, %rdx
#endif

// Save extra registers

        pushq   %rbx
        pushq   %r12

// If the input is already <= 3 words long, go to a trivial "copy" path

        cmpq    $4, k
        jc      bignum_mod_sm2_shortinput

// Otherwise load the top 4 digits (top-down) and reduce k by 4

        subq    $4, k
        movq    24(x,k,8), m3
        movq    16(x,k,8), m2
        movq    8(x,k,8), m1
        movq    (x,k,8), m0

// Load non-trivial digits [n3; -1; n1; -1] = p_sm2 and do a conditional
// subtraction to reduce the four starting digits [m3;m2;m1;m0] modulo p_sm2

        subq    $-1, m0
        movq    $0xffffffff00000000, n1
        sbbq    n1, m1
        movq    $0xfffffffeffffffff, n3
        sbbq    $-1, m2
        sbbq    n3, m3

        sbbq    n0, n0

        andq    n0, n1
        andq    n0, n3
        addq    n0, m0
        adcq    n1, m1
        adcq    n0, m2
        adcq    n3, m3

// Now do (k-4) iterations of 5->4 word modular reduction

        testq   k, k
        jz      bignum_mod_sm2_writeback

bignum_mod_sm2_loop:

// Writing the input, with the new zeroth digit implicitly appended, as
// z = 2^256 * m3 + 2^192 * m2 + t, our intended quotient approximation is
// MIN ((m3 * (1 + 2^32 + 2^64) + m2 + 2^64) >> 64) (2^64 - 1)

        movq    m2, d
        movl    $1, qshort
        addq    m3, d
        adcq    m3, q

        shrq    $32, d
        addq    m3, d

        shrq    $32, d
        addq    d, q
        sbbq    $0, q

// Load the next digit so current m to reduce = [m3;m2;m1;m0;d]

        movq    -8(x,k,8), d

// Now compute the initial pre-reduced [m3;m2;m1;m0;d] = m - p_sm2 * q
// = z - (2^256 - 2^224 - 2^96 + 2^64 - 1) * q

        movq    q, n0
        movq    q, n1
        shlq    $32, n0
        shrq    $32, n1

        addq    n0, m2
        adcq    n1, m3

        subq    q, n0
        sbbq    $0, n1

        subq    q, m3

        addq    q, d
        adcq    n0, m0
        adcq    n1, m1
        adcq    $0, m2
        adcq    $0, m3

// Now our top word m3 is either zero or all 1s, and we use this to discriminate
// whether a correction is needed because our result is negative, as a bitmask
// Do a masked addition of p_sm2

        movq    $0xffffffff00000000, n1
        andq    m3, n1
        movq    $0xfffffffeffffffff, n3
        andq    m3, n3
        addq    m3, d
        adcq    n1, m0
        adcq    m3, m1
        adcq    n3, m2

// Shuffle registers up and loop

        movq    m2, m3
        movq    m1, m2
        movq    m0, m1
        movq    d, m0

        decq    k
        jnz     bignum_mod_sm2_loop

// Write back

bignum_mod_sm2_writeback:

        movq    m0, (z)
        movq    m1, 8(z)
        movq    m2, 16(z)
        movq    m3, 24(z)

// Restore registers and return

        popq    %r12
        popq    %rbx
#if WINDOWS_ABI
        popq   %rsi
        popq   %rdi
#endif
        ret

bignum_mod_sm2_shortinput:

        xorq    m0, m0
        xorq    m1, m1
        xorq    m2, m2
        xorq    m3, m3

        testq   k, k
        jz      bignum_mod_sm2_writeback
        movq    (%rdx), m0
        decq    k
        jz      bignum_mod_sm2_writeback
        movq    8(%rdx), m1
        decq    k
        jz      bignum_mod_sm2_writeback
        movq    16(%rdx), m2
        jmp     bignum_mod_sm2_writeback

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
