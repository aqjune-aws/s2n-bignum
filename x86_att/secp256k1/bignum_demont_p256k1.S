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
// Convert from Montgomery form z := (x / 2^256) mod p_256k1,
// assuming x reduced
// Input x[4]; output z[4]
//
//    extern void bignum_demont_p256k1
//     (uint64_t z[static 4], uint64_t x[static 4]);
//
// This assumes the input is < p_256k1 for correctness. If this is not the
// case, use the variant "bignum_deamont_p256k1" instead.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// ----------------------------------------------------------------------------


        .globl  bignum_demont_p256k1
        .text

#define z %rdi
#define x %rsi

// Re-use x variable for the negated multiplicative inverse of p_256k1

#define w %rsi

// The rotating registers for the 4 digits

#define d0 %r8
#define d1 %r9
#define d2 %r10
#define d3 %r11

// Other variables. We need d == %rdx for mulx instructions

#define a %rax
#define d %rdx
#define c %rcx

bignum_demont_p256k1:

// Set up an initial 4-word window [d3,d2,d1,d0] = x

        movq    (x), d0
        movq    8(x), d1
        movq    16(x), d2
        movq    24(x), d3

// Set w to negated multiplicative inverse p_256k1 * w == -1 (mod 2^64).

        movq    $0xd838091dd2253531, w

// Four stages of Montgomery reduction, rotating the register window.
// Use c as a carry-catcher since the imul destroys the flags in general.

        imulq   w, d0
        movq    $4294968273, a
        mulq    d0
        subq    d, d1
        sbbq    c, c

        imulq   w, d1
        movq    $4294968273, a
        mulq    d1
        negq    c
        sbbq    d, d2
        sbbq    c, c

        imulq   w, d2
        movq    $4294968273, a
        mulq    d2
        negq    c
        sbbq    d, d3
        sbbq    c, c

        imulq   w, d3
        movq    $4294968273, a
        mulq    d3
        negq    c
        sbbq    d, d0

// Finish propagating carry through new top part, write back and return

        movq    d0, (z)
        sbbq    $0, d1
        movq    d1, 8(z)
        sbbq    $0, d2
        movq    d2, 16(z)
        sbbq    $0, d3
        movq    d3, 24(z)

        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif