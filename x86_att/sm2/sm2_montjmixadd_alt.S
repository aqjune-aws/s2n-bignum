// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Point mixed addition on GM/T 0003-2012 curve SM2 in Montgomery-Jacobian coordinates
//
//    extern void sm2_montjmixadd_alt(uint64_t p3[static 12],
//                                    const uint64_t p1[static 12],
//                                    const uint64_t p2[static 8]);
//
// Does p3 := p1 + p2 where all points are regarded as Jacobian triples with
// each coordinate in the Montgomery domain, i.e. x' = (2^256 * x) mod p_sm2.
// A Jacobian triple (x',y',z') represents affine point (x/z^2,y/z^3).
// The "mixed" part means that p2 only has x and y coordinates, with the
// implicit z coordinate assumed to be the identity.
//
// Standard x86-64 ABI: RDI = p3, RSI = p1, RDX = p2
// Microsoft x64 ABI:   RCX = p3, RDX = p1, R8 = p2
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(sm2_montjmixadd_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(sm2_montjmixadd_alt)
        .text

// Size of individual field elements

#define NUMSIZE 32

// Pointer-offset pairs for inputs and outputs
// These assume %rdi = p3, %rsi = p1 and %rbp = p2,
// which needs to be set up explicitly before use.
// By design, none of the code macros modify any of
// these, so we maintain the assignments throughout.

#define x_1 0(%rsi)
#define y_1 NUMSIZE(%rsi)
#define z_1 (2*NUMSIZE)(%rsi)

#define x_2 0(%rbp)
#define y_2 NUMSIZE(%rbp)

#define x_3 0(%rdi)
#define y_3 NUMSIZE(%rdi)
#define z_3 (2*NUMSIZE)(%rdi)

// Pointer-offset pairs for temporaries, with some aliasing
// NSPACE is the total stack needed for these temporaries

#define zp2 (NUMSIZE*0)(%rsp)
#define ww (NUMSIZE*0)(%rsp)
#define resx (NUMSIZE*0)(%rsp)

#define yd (NUMSIZE*1)(%rsp)
#define y2a (NUMSIZE*1)(%rsp)

#define x2a (NUMSIZE*2)(%rsp)
#define zzx2 (NUMSIZE*2)(%rsp)

#define zz (NUMSIZE*3)(%rsp)
#define t1 (NUMSIZE*3)(%rsp)

#define t2 (NUMSIZE*4)(%rsp)
#define zzx1 (NUMSIZE*4)(%rsp)
#define resy (NUMSIZE*4)(%rsp)

#define xd (NUMSIZE*5)(%rsp)
#define resz (NUMSIZE*5)(%rsp)

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

// Additional macros to help with final multiplexing

#define testzero4(P)                            \
        movq    P, %rax ;                       \
        movq    8+P, %rdx ;                     \
        orq     16+P, %rax ;                    \
        orq     24+P, %rdx ;                    \
        orq     %rdx, %rax

#define mux4(r0,r1,r2,r3,PNE,PEQ)               \
        movq    PNE, r0 ;                      \
        movq    PEQ, %rax ;                     \
        cmovzq  %rax, r0 ;                        \
        movq    8+PNE, r1 ;                    \
        movq    8+PEQ, %rax ;                   \
        cmovzq  %rax, r1 ;                        \
        movq    16+PNE, r2 ;                   \
        movq    16+PEQ, %rax ;                  \
        cmovzq  %rax, r2 ;                        \
        movq    24+PNE, r3 ;                   \
        movq    24+PEQ, %rax ;                  \
        cmovzq  %rax, r3

#define load4(r0,r1,r2,r3,P)                    \
        movq    P, r0 ;                        \
        movq    8+P, r1 ;                      \
        movq    16+P, r2 ;                     \
        movq    24+P, r3

#define store4(P,r0,r1,r2,r3)                   \
        movq    r0, P ;                        \
        movq    r1, 8+P ;                      \
        movq    r2, 16+P ;                     \
        movq    r3, 24+P

S2N_BN_SYMBOL(sm2_montjmixadd_alt):
        _CET_ENDBR

#if WINDOWS_ABI
        pushq   %rdi
        pushq   %rsi
        movq    %rcx, %rdi
        movq    %rdx, %rsi
        movq    %r8, %rdx
#endif

// Save registers and make room on stack for temporary variables
// Put the input y in %rbp where it lasts throughout the main code.

        pushq  %rbx
        pushq  %rbp
        pushq  %r12
        pushq  %r13
        pushq  %r14
        pushq  %r15

        subq    $NSPACE, %rsp

        movq    %rdx, %rbp

// Main code, just a sequence of basic field operations
// 8 * multiply + 3 * square + 7 * subtract

        montsqr_sm2(zp2,z_1)

        montmul_sm2(y2a,z_1,y_2)
        montmul_sm2(x2a,zp2,x_2)
        montmul_sm2(y2a,zp2,y2a)

        sub_sm2(xd,x2a,x_1)

        sub_sm2(yd,y2a,y_1)

        montsqr_sm2(zz,xd)
        montsqr_sm2(ww,yd)

        montmul_sm2(zzx1,zz,x_1)
        montmul_sm2(zzx2,zz,x2a)

        sub_sm2(resx,ww,zzx1)
        sub_sm2(t1,zzx2,zzx1)

        montmul_sm2(resz,xd,z_1)

        sub_sm2(resx,resx,zzx2)

        sub_sm2(t2,zzx1,resx)

        montmul_sm2(t1,t1,y_1)
        montmul_sm2(t2,yd,t2)

        sub_sm2(resy,t2,t1)

// Test if z_1 = 0 to decide if p1 = 0 (up to projective equivalence)

        testzero4(z_1)

// Multiplex: if p1 <> 0 just copy the computed result from the staging area.
// If p1 = 0 then return the point p2 augmented with a z = 1 coordinate (in
// Montgomery form so not the simple constant 1 but rather 2^256 - p_sm2),
// hence giving 0 + p2 = p2 for the final result.

        mux4(%r8,%r9,%r10,%r11,resx,x_2)
        mux4(%r12,%r13,%r14,%r15,resy,y_2)

        store4(x_3,%r8,%r9,%r10,%r11)
        store4(y_3,%r12,%r13,%r14,%r15)

        load4(%r8,%r9,%r10,%r11,resz)
        movl    $1, %eax
        cmovzq  %rax, %r8
        movl    $0x00000000ffffffff, %eax
        cmovzq  %rax, %r9
        movl    $0, %eax
        cmovzq  %rax, %r10
        movq    $0x0000000100000000, %rax
        cmovzq  %rax, %r11

        store4(z_3,%r8,%r9,%r10,%r11)

// Restore stack and registers

        addq    $NSPACE, %rsp
        popq    %r15
        popq    %r14
        popq    %r13
        popq    %r12
        popq    %rbp
        popq    %rbx

#if WINDOWS_ABI
        popq   %rsi
        popq   %rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
