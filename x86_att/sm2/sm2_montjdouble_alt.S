// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Point doubling on GM/T 0003-2012 curve SM2 in Montgomery-Jacobian coordinates
//
//    extern void sm2_montjdouble_alt(uint64_t p3[static 12],
//                                    const uint64_t p1[static 12]);
//
// Does p3 := 2 * p1 where all points are regarded as Jacobian triples with
// each coordinate in the Montgomery domain, i.e. x' = (2^256 * x) mod p_sm2.
// A Jacobian triple (x',y',z') represents affine point (x/z^2,y/z^3).
//
// Standard x86-64 ABI: RDI = p3, RSI = p1
// Microsoft x64 ABI:   RCX = p3, RDX = p1
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(sm2_montjdouble_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(sm2_montjdouble_alt)
        .text
        .balign 4

// Size of individual field elements

#define NUMSIZE 32

// Pointer-offset pairs for inputs and outputs
// These assume %rdi = p3, %rsi = p1, which is true when the
// arguments come in initially and is not disturbed throughout.

#define x_1 0(%rsi)
#define y_1 NUMSIZE(%rsi)
#define z_1 (2*NUMSIZE)(%rsi)

#define x_3 0(%rdi)
#define y_3 NUMSIZE(%rdi)
#define z_3 (2*NUMSIZE)(%rdi)

// Pointer-offset pairs for temporaries, with some aliasing
// NSPACE is the total stack needed for these temporaries

#define z2 (NUMSIZE*0)(%rsp)
#define y4 (NUMSIZE*0)(%rsp)

#define y2 (NUMSIZE*1)(%rsp)

#define t1 (NUMSIZE*2)(%rsp)

#define t2 (NUMSIZE*3)(%rsp)
#define x2p (NUMSIZE*3)(%rsp)
#define dx2 (NUMSIZE*3)(%rsp)

#define xy2 (NUMSIZE*4)(%rsp)

#define x4p (NUMSIZE*5)(%rsp)
#define d (NUMSIZE*5)(%rsp)

#define NSPACE (NUMSIZE*6)

// Corresponds to bignum_montmul_sm2_alt except for registers

#define montmul_sm2(P0,P1,P2)                   \
        movq    P1, %rax ;                      \
        mulq     P2;                 \
        movq    %rax, %r8 ;                        \
        movq    %rdx, %r9 ;                        \
        xorq    %r10, %r10 ;                       \
        xorq    %r11, %r11 ;                       \
        movq    P1, %rax ;                      \
        mulq     0x8+P2;             \
        addq    %rax, %r9 ;                        \
        adcq    %rdx, %r10 ;                       \
        movq    0x8+P1, %rax ;                  \
        mulq     P2;                 \
        addq    %rax, %r9 ;                        \
        adcq    %rdx, %r10 ;                       \
        adcq    %r11, %r11 ;                       \
        xorq    %r12, %r12 ;                       \
        movq    P1, %rax ;                      \
        mulq     0x10+P2;            \
        addq    %rax, %r10 ;                       \
        adcq    %rdx, %r11 ;                       \
        adcq    %r12, %r12 ;                       \
        movq    0x8+P1, %rax ;                  \
        mulq     0x8+P2;             \
        addq    %rax, %r10 ;                       \
        adcq    %rdx, %r11 ;                       \
        adcq    $0x0, %r12 ;                       \
        movq    0x10+P1, %rax ;                 \
        mulq     P2;                 \
        addq    %rax, %r10 ;                       \
        adcq    %rdx, %r11 ;                       \
        adcq    $0x0, %r12 ;                       \
        xorq    %r13, %r13 ;                       \
        movq    P1, %rax ;                      \
        mulq     0x18+P2;            \
        addq    %rax, %r11 ;                       \
        adcq    %rdx, %r12 ;                       \
        adcq    %r13, %r13 ;                       \
        movq    0x8+P1, %rax ;                  \
        mulq     0x10+P2;            \
        addq    %rax, %r11 ;                       \
        adcq    %rdx, %r12 ;                       \
        adcq    $0x0, %r13 ;                       \
        movq    0x10+P1, %rax ;                 \
        mulq     0x8+P2;             \
        addq    %rax, %r11 ;                       \
        adcq    %rdx, %r12 ;                       \
        adcq    $0x0, %r13 ;                       \
        movq    0x18+P1, %rax ;                 \
        mulq     P2;                 \
        addq    %rax, %r11 ;                       \
        adcq    %rdx, %r12 ;                       \
        adcq    $0x0, %r13 ;                       \
        xorq    %r14, %r14 ;                       \
        movq    0x8+P1, %rax ;                  \
        mulq     0x18+P2;            \
        addq    %rax, %r12 ;                       \
        adcq    %rdx, %r13 ;                       \
        adcq    %r14, %r14 ;                       \
        movq    0x10+P1, %rax ;                 \
        mulq     0x10+P2;            \
        addq    %rax, %r12 ;                       \
        adcq    %rdx, %r13 ;                       \
        adcq    $0x0, %r14 ;                       \
        movq    0x18+P1, %rax ;                 \
        mulq     0x8+P2;             \
        addq    %rax, %r12 ;                       \
        adcq    %rdx, %r13 ;                       \
        adcq    $0x0, %r14 ;                       \
        xorq    %r15, %r15 ;                       \
        movq    0x10+P1, %rax ;                 \
        mulq     0x18+P2;            \
        addq    %rax, %r13 ;                       \
        adcq    %rdx, %r14 ;                       \
        adcq    %r15, %r15 ;                       \
        movq    0x18+P1, %rax ;                 \
        mulq     0x10+P2;            \
        addq    %rax, %r13 ;                       \
        adcq    %rdx, %r14 ;                       \
        adcq    $0x0, %r15 ;                       \
        movq    0x18+P1, %rax ;                 \
        mulq     0x18+P2;            \
        addq    %rax, %r14 ;                       \
        adcq    %rdx, %r15 ;                       \
        movq    %r8, %rax ;                        \
        shlq    $0x20, %rax ;                      \
        movq    %r8, %rcx ;                        \
        shrq    $0x20, %rcx ;                      \
        movq    %rax, %rdx ;                       \
        movq    %rcx, %rbx ;                       \
        subq    %r8, %rax ;                        \
        sbbq    $0x0, %rcx ;                       \
        subq    %rax, %r9 ;                        \
        sbbq    %rcx, %r10 ;                       \
        sbbq    %rdx, %r11 ;                       \
        sbbq    %rbx, %r8 ;                        \
        movq    %r9, %rax ;                        \
        shlq    $0x20, %rax ;                      \
        movq    %r9, %rcx ;                        \
        shrq    $0x20, %rcx ;                      \
        movq    %rax, %rdx ;                       \
        movq    %rcx, %rbx ;                       \
        subq    %r9, %rax ;                        \
        sbbq    $0x0, %rcx ;                       \
        subq    %rax, %r10 ;                       \
        sbbq    %rcx, %r11 ;                       \
        sbbq    %rdx, %r8 ;                        \
        sbbq    %rbx, %r9 ;                        \
        movq    %r10, %rax ;                       \
        shlq    $0x20, %rax ;                      \
        movq    %r10, %rcx ;                       \
        shrq    $0x20, %rcx ;                      \
        movq    %rax, %rdx ;                       \
        movq    %rcx, %rbx ;                       \
        subq    %r10, %rax ;                       \
        sbbq    $0x0, %rcx ;                       \
        subq    %rax, %r11 ;                       \
        sbbq    %rcx, %r8 ;                        \
        sbbq    %rdx, %r9 ;                        \
        sbbq    %rbx, %r10 ;                       \
        movq    %r11, %rax ;                       \
        shlq    $0x20, %rax ;                      \
        movq    %r11, %rcx ;                       \
        shrq    $0x20, %rcx ;                      \
        movq    %rax, %rdx ;                       \
        movq    %rcx, %rbx ;                       \
        subq    %r11, %rax ;                       \
        sbbq    $0x0, %rcx ;                       \
        subq    %rax, %r8 ;                        \
        sbbq    %rcx, %r9 ;                        \
        sbbq    %rdx, %r10 ;                       \
        sbbq    %rbx, %r11 ;                       \
        xorl    %eax, %eax ;                       \
        addq    %r8, %r12 ;                        \
        adcq    %r9, %r13 ;                        \
        adcq    %r10, %r14 ;                       \
        adcq    %r11, %r15 ;                       \
        adcq    %rax, %rax ;                       \
        movl    $0x1, %ecx ;                       \
        movl    $0xffffffff, %edx ;                \
        xorl    %ebx, %ebx ;                       \
        addq    %r12, %rcx ;                       \
        leaq    0x1(%rdx), %r11 ;                 \
        adcq    %r13, %rdx ;                       \
        leaq    -0x1(%rbx), %r8 ;                  \
        adcq    %r14, %rbx ;                       \
        adcq    %r15, %r11 ;                       \
        adcq    %rax, %r8 ;                        \
        cmovbq  %rcx, %r12 ;                       \
        cmovbq  %rdx, %r13 ;                       \
        cmovbq  %rbx, %r14 ;                       \
        cmovbq  %r11, %r15 ;                       \
        movq    %r12, P0 ;                      \
        movq    %r13, 0x8+P0 ;                  \
        movq    %r14, 0x10+P0 ;                 \
        movq    %r15, 0x18+P0

// Corresponds to bignum_montsqr_sm2_alt except for registers

#define montsqr_sm2(P0,P1)                      \
        movq    P1, %rax ;                      \
        movq    %rax, %rbx ;                       \
        mulq    %rax;                            \
        movq    %rax, %r8 ;                        \
        movq    %rdx, %r15 ;                       \
        movq    0x8+P1, %rax ;                  \
        mulq    %rbx;                            \
        movq    %rax, %r9 ;                        \
        movq    %rdx, %r10 ;                       \
        movq    0x18+P1, %rax ;                 \
        movq    %rax, %r13 ;                       \
        mulq    %rbx;                            \
        movq    %rax, %r11 ;                       \
        movq    %rdx, %r12 ;                       \
        movq    0x10+P1, %rax ;                 \
        movq    %rax, %rbx ;                       \
        mulq    %r13;                            \
        movq    %rax, %r13 ;                       \
        movq    %rdx, %r14 ;                       \
        movq    P1, %rax ;                      \
        mulq    %rbx;                            \
        addq    %rax, %r10 ;                       \
        adcq    %rdx, %r11 ;                       \
        sbbq    %rcx, %rcx ;                       \
        movq    0x8+P1, %rax ;                  \
        mulq    %rbx;                            \
        subq    %rcx, %rdx ;                       \
        addq    %rax, %r11 ;                       \
        adcq    %rdx, %r12 ;                       \
        sbbq    %rcx, %rcx ;                       \
        movq    0x18+P1, %rbx ;                 \
        movq    0x8+P1, %rax ;                  \
        mulq    %rbx;                            \
        subq    %rcx, %rdx ;                       \
        addq    %rax, %r12 ;                       \
        adcq    %rdx, %r13 ;                       \
        adcq    $0x0, %r14 ;                       \
        xorl    %ecx, %ecx ;                       \
        addq    %r9, %r9 ;                         \
        adcq    %r10, %r10 ;                       \
        adcq    %r11, %r11 ;                       \
        adcq    %r12, %r12 ;                       \
        adcq    %r13, %r13 ;                       \
        adcq    %r14, %r14 ;                       \
        adcq    %rcx, %rcx ;                       \
        movq    0x8+P1, %rax ;                  \
        mulq    %rax;                            \
        addq    %r15, %r9 ;                        \
        adcq    %rax, %r10 ;                       \
        adcq    %rdx, %r11 ;                       \
        sbbq    %r15, %r15 ;                       \
        movq    0x10+P1, %rax ;                 \
        mulq    %rax;                            \
        negq    %r15;                            \
        adcq    %rax, %r12 ;                       \
        adcq    %rdx, %r13 ;                       \
        sbbq    %r15, %r15 ;                       \
        movq    0x18+P1, %rax ;                 \
        mulq    %rax;                            \
        negq    %r15;                            \
        adcq    %rax, %r14 ;                       \
        adcq    %rcx, %rdx ;                       \
        movq    %rdx, %r15 ;                       \
        movq    %r8, %rax ;                        \
        shlq    $0x20, %rax ;                      \
        movq    %r8, %rcx ;                        \
        shrq    $0x20, %rcx ;                      \
        movq    %rax, %rdx ;                       \
        movq    %rcx, %rbx ;                       \
        subq    %r8, %rax ;                        \
        sbbq    $0x0, %rcx ;                       \
        subq    %rax, %r9 ;                        \
        sbbq    %rcx, %r10 ;                       \
        sbbq    %rdx, %r11 ;                       \
        sbbq    %rbx, %r8 ;                        \
        movq    %r9, %rax ;                        \
        shlq    $0x20, %rax ;                      \
        movq    %r9, %rcx ;                        \
        shrq    $0x20, %rcx ;                      \
        movq    %rax, %rdx ;                       \
        movq    %rcx, %rbx ;                       \
        subq    %r9, %rax ;                        \
        sbbq    $0x0, %rcx ;                       \
        subq    %rax, %r10 ;                       \
        sbbq    %rcx, %r11 ;                       \
        sbbq    %rdx, %r8 ;                        \
        sbbq    %rbx, %r9 ;                        \
        movq    %r10, %rax ;                       \
        shlq    $0x20, %rax ;                      \
        movq    %r10, %rcx ;                       \
        shrq    $0x20, %rcx ;                      \
        movq    %rax, %rdx ;                       \
        movq    %rcx, %rbx ;                       \
        subq    %r10, %rax ;                       \
        sbbq    $0x0, %rcx ;                       \
        subq    %rax, %r11 ;                       \
        sbbq    %rcx, %r8 ;                        \
        sbbq    %rdx, %r9 ;                        \
        sbbq    %rbx, %r10 ;                       \
        movq    %r11, %rax ;                       \
        shlq    $0x20, %rax ;                      \
        movq    %r11, %rcx ;                       \
        shrq    $0x20, %rcx ;                      \
        movq    %rax, %rdx ;                       \
        movq    %rcx, %rbx ;                       \
        subq    %r11, %rax ;                       \
        sbbq    $0x0, %rcx ;                       \
        subq    %rax, %r8 ;                        \
        sbbq    %rcx, %r9 ;                        \
        sbbq    %rdx, %r10 ;                       \
        sbbq    %rbx, %r11 ;                       \
        xorl    %eax, %eax ;                       \
        addq    %r8, %r12 ;                        \
        adcq    %r9, %r13 ;                        \
        adcq    %r10, %r14 ;                       \
        adcq    %r11, %r15 ;                       \
        adcq    %rax, %rax ;                       \
        movl    $0x1, %ecx ;                       \
        movl    $0xffffffff, %edx ;                \
        xorl    %ebx, %ebx ;                       \
        addq    %r12, %rcx ;                       \
        leaq    0x1(%rdx), %r11 ;                 \
        adcq    %r13, %rdx ;                       \
        leaq    -0x1(%rbx), %r8 ;                  \
        adcq    %r14, %rbx ;                       \
        adcq    %r15, %r11 ;                       \
        adcq    %rax, %r8 ;                        \
        cmovbq  %rcx, %r12 ;                       \
        cmovbq  %rdx, %r13 ;                       \
        cmovbq  %rbx, %r14 ;                       \
        cmovbq  %r11, %r15 ;                       \
        movq    %r12, P0 ;                      \
        movq    %r13, 0x8+P0 ;                  \
        movq    %r14, 0x10+P0 ;                 \
        movq    %r15, 0x18+P0

// Corresponds exactly to bignum_sub_sm2

#define sub_sm2(P0,P1,P2)                       \
        movq    P1, %rax ;                      \
        subq    P2, %rax ;                      \
        movq    0x8+P1, %rcx ;                  \
        sbbq    0x8+P2, %rcx ;                  \
        movq    0x10+P1, %r8 ;                  \
        sbbq    0x10+P2, %r8 ;                  \
        movq    0x18+P1, %r9 ;                  \
        sbbq    0x18+P2, %r9 ;                  \
        movq    $0xffffffff00000000, %r10 ;        \
        sbbq    %r11, %r11 ;                       \
        andq    %r11, %r10 ;                       \
        movq    %r11, %rdx ;                       \
        btr     $0x20, %rdx ;                      \
        addq    %r11, %rax ;                       \
        movq    %rax, P0 ;                      \
        adcq    %r10, %rcx ;                       \
        movq    %rcx, 0x8+P0 ;                  \
        adcq    %r11, %r8 ;                        \
        movq    %r8, 0x10+P0 ;                  \
        adcq    %rdx, %r9 ;                        \
        movq    %r9, 0x18+P0

// Corresponds exactly to bignum_add_sm2

#define add_sm2(P0,P1,P2)                       \
        xorq    %r11, %r11 ;                       \
        movq    P1, %rax ;                      \
        addq    P2, %rax ;                      \
        movq    0x8+P1, %rcx ;                  \
        adcq    0x8+P2, %rcx ;                  \
        movq    0x10+P1, %r8 ;                  \
        adcq    0x10+P2, %r8 ;                  \
        movq    0x18+P1, %r9 ;                  \
        adcq    0x18+P2, %r9 ;                  \
        adcq    %r11, %r11 ;                       \
        subq    $0xffffffffffffffff, %rax ;        \
        movq    $0xffffffff00000000, %r10 ;        \
        sbbq    %r10, %rcx ;                       \
        sbbq    $0xffffffffffffffff, %r8 ;         \
        movq    $0xfffffffeffffffff, %rdx ;        \
        sbbq    %rdx, %r9 ;                        \
        sbbq    $0x0, %r11 ;                       \
        andq    %r11, %r10 ;                       \
        andq    %r11, %rdx ;                       \
        addq    %r11, %rax ;                       \
        movq    %rax, P0 ;                      \
        adcq    %r10, %rcx ;                       \
        movq    %rcx, 0x8+P0 ;                  \
        adcq    %r11, %r8 ;                        \
        movq    %r8, 0x10+P0 ;                  \
        adcq    %rdx, %r9 ;                        \
        movq    %r9, 0x18+P0

// A weak version of add that only guarantees sum in 4 digits

#define weakadd_sm2(P0,P1,P2)                   \
        movq    P1, %rax ;                      \
        addq    P2, %rax ;                      \
        movq    0x8+P1, %rcx ;                  \
        adcq    0x8+P2, %rcx ;                  \
        movq    0x10+P1, %r8 ;                  \
        adcq    0x10+P2, %r8 ;                  \
        movq    0x18+P1, %r9 ;                  \
        adcq    0x18+P2, %r9 ;                  \
        movq    $0xffffffff00000000, %r10 ;        \
        sbbq    %r11, %r11 ;                       \
        andq    %r11, %r10 ;                       \
        movq    %r11, %rdx ;                       \
        btr     $0x20, %rdx ;                      \
        subq    %r11, %rax ;                       \
        movq    %rax, P0 ;                      \
        sbbq    %r10, %rcx ;                       \
        movq    %rcx, 0x8+P0 ;                  \
        sbbq    %r11, %r8 ;                        \
        movq    %r8, 0x10+P0 ;                  \
        sbbq    %rdx, %r9 ;                        \
        movq    %r9, 0x18+P0

// P0 = C * P1 - D * P2  computed as d * (p_sm2 - P2) + c * P1
// Quotient estimation is done just as q = h + 1 as in bignum_triple_sm2
// This also applies to the other functions following.

#define cmsub_sm2(P0,C,P1,D,P2)                \
        /* First (%r12;%r11;%r10;%r9) = p_sm2 - P2 */ \
        movq    $0xffffffffffffffff, %r9 ;          \
        movq    %r9, %r11 ;                        \
        subq    P2, %r9 ;                        \
        movq    $0xffffffff00000000, %r10 ;         \
        sbbq    0x8+P2, %r10 ;                   \
        sbbq    0x10+P2, %r11 ;                  \
        movq    $0xfffffffeffffffff, %r12 ;         \
        sbbq    0x18+P2, %r12 ;                  \
        /* (%r12;%r11;%r10;%r9;%r8) = D * (p_sm2 - P2) */  \
        movq    $D, %rcx ;                         \
        movq    %r9, %rax ;                        \
        mulq    %rcx;                            \
        movq    %rax, %r8 ;                        \
        movq    %rdx, %r9 ;                        \
        movq    %r10, %rax ;                       \
        xorl    %r10d, %r10d ;                     \
        mulq    %rcx;                            \
        addq    %rax, %r9 ;                        \
        adcq    %rdx, %r10 ;                       \
        movq    %r11, %rax ;                       \
        xorl    %r11d, %r11d ;                     \
        mulq    %rcx;                            \
        addq    %rax, %r10 ;                       \
        adcq    %rdx, %r11 ;                       \
        movq    %r12, %rax ;                       \
        xorl    %r12d, %r12d ;                     \
        mulq    %rcx;                            \
        addq    %rax, %r11 ;                       \
        adcq    %rdx, %r12 ;                       \
        /* (%rdx;%r11;%r10;%r9;%r8) = 2^256 + C * P1 + D * (p_sm2 - P2) */ \
        movl    $C, %ecx ;                         \
        movq    P1, %rax ;                      \
        mulq    %rcx;                            \
        addq    %rax, %r8 ;                        \
        adcq    %rdx, %r9 ;                        \
        sbbq    %rbx, %rbx ;                       \
        movq    0x8+P1, %rax ;                  \
        mulq    %rcx;                            \
        subq    %rbx, %rdx ;                       \
        addq    %rax, %r9 ;                        \
        adcq    %rdx, %r10 ;                       \
        sbbq    %rbx, %rbx ;                       \
        movq    0x10+P1, %rax ;                 \
        mulq    %rcx;                            \
        subq    %rbx, %rdx ;                       \
        addq    %rax, %r10 ;                       \
        adcq    %rdx, %r11 ;                       \
        sbbq    %rbx, %rbx ;                       \
        movq    0x18+P1, %rax ;                 \
        mulq    %rcx;                            \
        subq    %rbx, %rdx ;                       \
        addq    %rax, %r11 ;                       \
        adcq    %rdx, %r12 ;                       \
        leaq    1(%r12), %rdx ;                   \
        /* Now the tail for modular reduction from tripling */ \
        movq    %rdx, %rax ;                       \
        shlq    $0x20, %rax ;                      \
        movq    %rax, %rcx ;                       \
        subq    %rdx, %rax ;                       \
        addq    %rdx, %r8 ;                        \
        adcq    %rax, %r9 ;                        \
        adcq    $0x0, %r10 ;                       \
        adcq    %rcx, %r11 ;                       \
        sbbq    %rdx, %rdx ;                       \
        notq    %rdx;                            \
        movq    $0xffffffff00000000, %rax ;        \
        andq    %rdx, %rax ;                       \
        movq    %rdx, %rcx ;                       \
        btr     $0x20, %rcx ;                      \
        addq    %rdx, %r8 ;                        \
        movq    %r8, P0 ;                       \
        adcq    %rax, %r9 ;                        \
        movq    %r9, 0x8+P0 ;                   \
        adcq    %rdx, %r10 ;                       \
        movq    %r10, 0x10+P0 ;                 \
        adcq    %rcx, %r11 ;                       \
        movq    %r11, 0x18+P0

// P0 = 3 * P1 - 8 * P2, computed as (p_sm2 - P2) << 3 + 3 * P1

#define cmsub38_sm2(P0,P1,P2)                  \
        /* First (%r11;%r10;%r9;%r8) = p_sm2 - P2 */ \
        movq    $0xffffffffffffffff, %r8 ;          \
        movq    %r8, %r10 ;                        \
        subq    P2, %r8 ;                        \
        movq    $0xffffffff00000000, %r9 ;          \
        sbbq    0x8+P2, %r9 ;                    \
        sbbq    0x10+P2, %r10 ;                  \
        movq    $0xfffffffeffffffff, %r11 ;         \
        sbbq    0x18+P2, %r11 ;                  \
        /* (%r12;%r11;%r10;%r9;%r8) = (p_sm2 - P2) << 3 */  \
        movq    %r11, %r12 ;                       \
        shldq   $3, %r10, %r11 ;                    \
        shldq   $3, %r9, %r10 ;                     \
        shldq   $3, %r8, %r9 ;                      \
        shlq    $3, %r8 ;                          \
        shrq    $61, %r12 ;                        \
        /* (%rdx;%r11;%r10;%r9;%r8) = 2^256 + 3 * P1 + 8 * (p_sm2 - P2) */ \
        movl    $3, %ecx ;                         \
        movq    P1, %rax ;                      \
        mulq    %rcx;                            \
        addq    %rax, %r8 ;                        \
        adcq    %rdx, %r9 ;                        \
        sbbq    %rbx, %rbx ;                       \
        movq    0x8+P1, %rax ;                  \
        mulq    %rcx;                            \
        subq    %rbx, %rdx ;                       \
        addq    %rax, %r9 ;                        \
        adcq    %rdx, %r10 ;                       \
        sbbq    %rbx, %rbx ;                       \
        movq    0x10+P1, %rax ;                 \
        mulq    %rcx;                            \
        subq    %rbx, %rdx ;                       \
        addq    %rax, %r10 ;                       \
        adcq    %rdx, %r11 ;                       \
        sbbq    %rbx, %rbx ;                       \
        movq    0x18+P1, %rax ;                 \
        mulq    %rcx;                            \
        subq    %rbx, %rdx ;                       \
        addq    %rax, %r11 ;                       \
        adcq    %rdx, %r12 ;                       \
        leaq    1(%r12), %rdx ;                   \
        /* Now the tail for modular reduction from tripling */ \
        movq    %rdx, %rax ;                       \
        shlq    $0x20, %rax ;                      \
        movq    %rax, %rcx ;                       \
        subq    %rdx, %rax ;                       \
        addq    %rdx, %r8 ;                        \
        adcq    %rax, %r9 ;                        \
        adcq    $0x0, %r10 ;                       \
        adcq    %rcx, %r11 ;                       \
        sbbq    %rdx, %rdx ;                       \
        notq    %rdx;                            \
        movq    $0xffffffff00000000, %rax ;        \
        andq    %rdx, %rax ;                       \
        movq    %rdx, %rcx ;                       \
        btr     $0x20, %rcx ;                      \
        addq    %rdx, %r8 ;                        \
        movq    %r8, P0 ;                       \
        adcq    %rax, %r9 ;                        \
        movq    %r9, 0x8+P0 ;                   \
        adcq    %rdx, %r10 ;                       \
        movq    %r10, 0x10+P0 ;                 \
        adcq    %rcx, %r11 ;                       \
        movq    %r11, 0x18+P0

// P0 = 4 * P1 - P2, by direct subtraction of P2,
// since the quotient estimate still works safely
// for initial value > -p_sm2

#define cmsub41_sm2(P0,P1,P2)                  \
        movq    0x18+P1, %r11 ;                  \
        movq    %r11, %rdx ;                       \
        movq    0x10+P1, %r10 ;                  \
        shldq   $2, %r10, %r11 ;                    \
        movq    0x8+P1, %r9 ;                    \
        shldq   $2, %r9, %r10 ;                     \
        movq    P1, %r8 ;                        \
        shldq   $2, %r8, %r9 ;                      \
        shlq    $2, %r8 ;                          \
        shrq    $62, %rdx ;                        \
        addq    $1, %rdx ;                         \
        subq    P2, %r8 ;                       \
        sbbq    0x8+P2, %r9 ;                   \
        sbbq    0x10+P2, %r10 ;                 \
        sbbq    0x18+P2, %r11 ;                 \
        sbbq    $0, %rdx ;                         \
        /* Now the tail for modular reduction from tripling */ \
        movq    %rdx, %rax ;                       \
        shlq    $0x20, %rax ;                      \
        movq    %rax, %rcx ;                       \
        subq    %rdx, %rax ;                       \
        addq    %rdx, %r8 ;                        \
        adcq    %rax, %r9 ;                        \
        adcq    $0x0, %r10 ;                       \
        adcq    %rcx, %r11 ;                       \
        sbbq    %rdx, %rdx ;                       \
        notq    %rdx;                            \
        movq    $0xffffffff00000000, %rax ;        \
        andq    %rdx, %rax ;                       \
        movq    %rdx, %rcx ;                       \
        btr     $0x20, %rcx ;                      \
        addq    %rdx, %r8 ;                        \
        movq    %r8, P0 ;                       \
        adcq    %rax, %r9 ;                        \
        movq    %r9, 0x8+P0 ;                   \
        adcq    %rdx, %r10 ;                       \
        movq    %r10, 0x10+P0 ;                 \
        adcq    %rcx, %r11 ;                       \
        movq    %r11, 0x18+P0

S2N_BN_SYMBOL(sm2_montjdouble_alt):
        _CET_ENDBR

#if WINDOWS_ABI
        pushq   %rdi
        pushq   %rsi
        movq    %rcx, %rdi
        movq    %rdx, %rsi
#endif

// Save registers and make room on stack for temporary variables

        pushq  %rbx
        pushq  %r12
        pushq  %r13
        pushq  %r14
        pushq  %r15

        subq    $NSPACE, %rsp

// Main code, just a sequence of basic field operations

// z2 = z^2
// y2 = y^2

        montsqr_sm2(z2,z_1)
        montsqr_sm2(y2,y_1)

// x2p = x^2 - z^4 = (x + z^2) * (x - z^2)

        sub_sm2(t2,x_1,z2)
        weakadd_sm2(t1,x_1,z2)
        montmul_sm2(x2p,t1,t2)

// t1 = y + z
// xy2 = x * y^2
// x4p = x2p^2

        add_sm2(t1,y_1,z_1)
        montmul_sm2(xy2,x_1,y2)
        montsqr_sm2(x4p,x2p)

// t1 = (y + z)^2

        montsqr_sm2(t1,t1)

// d = 12 * xy2 - 9 * x4p
// t1 = y^2 + 2 * y * z

        cmsub_sm2(d,12,xy2,9,x4p)
        sub_sm2(t1,t1,z2)

// y4 = y^4

        montsqr_sm2(y4,y2)

// dx2 = d * x2p

        montmul_sm2(dx2,d,x2p)

// z_3' = 2 * y * z

        sub_sm2(z_3,t1,y2)

// x' = 4 * xy2 - d

        cmsub41_sm2(x_3,xy2,d)

// y' = 3 * dx2 - 8 * y4

        cmsub38_sm2(y_3,dx2,y4)

// Restore stack and registers

        addq    $NSPACE, %rsp
        popq    %r15
        popq    %r14
        popq    %r13
        popq    %r12
        popq    %rbx

#if WINDOWS_ABI
        popq   %rsi
        popq   %rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
