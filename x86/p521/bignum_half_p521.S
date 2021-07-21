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
// Halve modulo p_521, z := (x / 2) mod p_521, assuming x reduced
// Input x[9]; output z[9]
//
//    extern void bignum_half_p521
//     (uint64_t z[static 9], uint64_t x[static 9]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// ----------------------------------------------------------------------------

#define z rdi
#define x rsi

// We use distinct variables for clarity, but these are heavily aliased

#define d0 rcx
#define d1 rdx
#define d2 rcx
#define d3 rdx
#define d4 rcx
#define d5 rdx
#define d6 rcx
#define d7 rdx
#define d8 rcx
#define a rax
#define ashort eax

.intel_syntax noprefix

        .globl bignum_half_p521
        .text

bignum_half_p521:

// We do a 521-bit rotation one bit right, since 2^521 == 1 (mod p_521)

                mov     d0, [x]
                mov     ashort, 1
                and     a, d0

                mov     d1, [x+8]
                shrd    d0, d1, 1
                mov     [z], d0

                mov     d2, [x+16]
                shrd    d1, d2, 1
                mov     [z+8], d1

                mov     d3, [x+24]
                shrd    d2, d3, 1
                mov     [z+16], d2

                mov     d4, [x+32]
                shrd    d3, d4, 1
                mov     [z+24], d3

                mov     d5, [x+40]
                shrd    d4, d5, 1
                mov     [z+32], d4

                mov     d6, [x+48]
                shrd    d5, d6, 1
                mov     [z+40], d5

                mov     d7, [x+56]
                shrd    d6, d7, 1
                mov     [z+48], d6

                mov     d8, [x+64]
                shrd    d7, d8, 1
                mov     [z+56], d7

                shl     d8, 55
                shrd    d8, a, 56
                mov     [z+64], d8

// Return

                ret