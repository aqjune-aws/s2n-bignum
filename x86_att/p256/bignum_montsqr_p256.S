/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "LICENSE" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

// ----------------------------------------------------------------------------
// Montgomery square, z := (x^2 / 2^256) mod p_256
// Input x[4]; output z[4]
//
//    extern void bignum_montsqr_p256
//     (uint64_t z[static 4], uint64_t x[static 4]);
//
// Does z := (x^2 / 2^256) mod p_256, assuming x^2 <= 2^256 * p_256, which is
// guaranteed in particular if x < p_256 initially (the "intended" case).
//
// Standard x86-64 ABI: RDI = z, RSI = x
// ----------------------------------------------------------------------------


        .globl  bignum_montsqr_p256
        .text

#define z %rdi
#define x %rsi

// Use this fairly consistently for a zero

#define zero %rbp
#define zeroe %ebp

// Add %rdx * m into a register-pair (high,low)
// maintaining consistent double-carrying with adcx and adox,
// using %rax and %rbx as temporaries

#define mulpadd(high,low,m)             \
        mulxq   m, %rax, %rbx ;            \
        adcxq   %rax, low ;               \
        adoxq   %rbx, high

bignum_montsqr_p256:

// Save more registers to play with

        pushq   %rbx
        pushq   %rbp
        pushq   %r12
        pushq   %r13
        pushq   %r14
        pushq   %r15

// Compute [%r15;%r8] = [00] which we use later, but mainly
// set up an initial window [%r14;...;%r9] = [23;03;01]

        movq    (x), %rdx
        mulxq   %rdx, %r8, %r15
        mulxq   8(x), %r9, %r10
        mulxq   24(x), %r11, %r12
        movq    16(x), %rdx
        mulxq   24(x), %r13, %r14

// Clear our zero register, and also initialize the flags for the carry chain

        xorl    zeroe, zeroe

// Chain in the addition of 02 + 12 + 13 to that window (no carry-out possible)
// This gives all the "heterogeneous" terms of the squaring ready to double

        mulpadd (%r11,%r10,(x))
        mulpadd (%r12,%r11,8(x))
        movq    24(x), %rdx
        mulpadd (%r13,%r12,8(x))
        adcxq   zero, %r13
        adoxq   zero, %r14
        adcq    zero, %r14

// Double and add to the 00 + 11 + 22 + 33 terms

        xorl    zeroe, zeroe
        adcxq   %r9, %r9
        adoxq   %r15, %r9
        movq    8(x), %rdx
        mulxq   %rdx, %rax, %rdx
        adcxq   %r10, %r10
        adoxq   %rax, %r10
        adcxq   %r11, %r11
        adoxq   %rdx, %r11
        movq    16(x), %rdx
        mulxq   %rdx, %rax, %rdx
        adcxq   %r12, %r12
        adoxq   %rax, %r12
        adcxq   %r13, %r13
        adoxq   %rdx, %r13
        movq    24(x), %rdx
        mulxq   %rdx, %rax, %r15
        adcxq   %r14, %r14
        adoxq   %rax, %r14
        adcxq   zero, %r15
        adoxq   zero, %r15

// First two waves of Montgomery reduction. Consolidate the double carries
// in %r9 and propagate up to the top in %r8, which is no longer needed otherwise.

        xorl    zeroe, zeroe
        movq    $0x0000000100000000, %rdx
        mulpadd (%r10,%r9,%r8)
        mulpadd (%r11,%r10,%r9)
        movq    $0xffffffff00000001, %rdx
        mulpadd (%r12,%r11,%r8)
        mulpadd (%r13,%r12,%r9)
        adcxq   zero, %r13
        movl    zeroe, %r9d
        adoxq   zero, %r9
        adcxq   zero, %r9
        addq    %r9, %r14
        adcq    zero, %r15
        movl    zeroe, %r8d
        adcq    zero, %r8

// Now two more steps of Montgomery reduction, again with %r8 = top carry

        xorl    zeroe, zeroe
        movq    $0x0000000100000000, %rdx
        mulpadd (%r12,%r11,%r10)
        mulpadd (%r13,%r12,%r11)
        movq    $0xffffffff00000001, %rdx
        mulpadd (%r14,%r13,%r10)
        mulpadd (%r15,%r14,%r11)
        adcxq   zero, %r15
        adoxq   zero, %r8
        adcq    zero, %r8

// Load [%rax;%r11;%rbp;%rdx;%rcx] = 2^320 - p_256, re-using earlier numbers a bit
// Do [%rax;%r11;%rbp;%rdx;%rcx] = [%r8;%r15;%r14;%r13;%r12] + (2^320 - p_256)

        movl    $1, %ecx
        addq    %r12, %rcx
        leaq    -1(%rdx), %rdx
        adcq    %r13, %rdx
        leaq    -1(%rbp), %rbp
        movq    %rbp, %rax
        adcq    %r14, %rbp
        movl    $0x00000000fffffffe, %r11d
        adcq    %r15, %r11
        adcq    %r8, %rax

// Now carry is set if r + (2^320 - p_256) >= 2^320, i.e. r >= p_256
// where r is the pre-reduced form. So conditionally select the
// output accordingly.

        cmovcq  %rcx, %r12
        cmovcq  %rdx, %r13
        cmovcq  %rbp, %r14
        cmovcq  %r11, %r15

// Write back reduced value

        movq    %r12, (z)
        movq    %r13, 8(z)
        movq    %r14, 16(z)
        movq    %r15, 24(z)

// Restore saved registers and return

        popq    %r15
        popq    %r14
        popq    %r13
        popq    %r12
        popq    %rbp
        popq    %rbx

        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif