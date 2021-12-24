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
// Negate modulo p_256k1, z := (-x) mod p_256k1, assuming x reduced
// Input x[4]; output z[4]
//
//    extern void bignum_neg_p256k1
//     (uint64_t z[static 4], uint64_t x[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// ----------------------------------------------------------------------------


        .globl  bignum_neg_p256k1
        .text

#define z %rdi
#define x %rsi

#define q %rdx
#define n0 %rax
#define n1 %rcx
#define n2 %r8
#define n3 %r9

#define c %r10

#define qshort %esi

bignum_neg_p256k1:

// Load the 4 digits of x and let q be an OR of all the digits

                movq    (x), n0
                movq    n0, q
                movq    8(x), n1
                orq     n1, q
                movq    16(x), n2
                orq     n2, q
                movq    24(x), n3
                orq     n3, q

// Turn q into a strict bitmask, and c a masked constant -4294968273

                negq    q
                sbbq    q, q
                movq    $-4294968273, c
                andq    q, c

// Now just do [2^256 - 4294968273] - x where the constant is masked

                subq    n0, c
                movq    c, (z)
                movq    q, c
                sbbq    n1, c
                movq    c, 8(z)
                movq    q, c
                sbbq    n2, c
                movq    c, 16(z)
                sbbq    n3, q
                movq    q, 24(z)

                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif