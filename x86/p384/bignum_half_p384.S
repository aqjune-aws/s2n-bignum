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
// Halve modulo p_384, z := (x / 2) mod p_384, assuming x reduced
// Input x[6]; output z[6]
//
//    extern void bignum_half_p384
//     (uint64_t z[static 6], uint64_t x[static 6]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// ----------------------------------------------------------------------------

#define z rdi
#define x rsi

#define a rax
#define d0 rcx
#define d1 rdx
#define d2 r8
#define d3 r9
#define d4 r10
#define d5 r11

#define d0short ecx
#define d3short r9d

.intel_syntax noprefix

        .globl bignum_half_p384
        .text

bignum_half_p384:

// Load lowest digit and get a mask for its lowest bit in d3

                mov     a, [x]
                mov     d3short, 1
                and     d3, a
                neg     d3

// Create a masked version of p_384 (top 3 words = the mask itself)

                mov     d0short, 0x00000000ffffffff
                and     d0, d3
                mov     d1, d0
                xor     d1, d3
                mov     d2, d3
                add     d2, d2
                and     d2, d3
                mov     d4, d3
                mov     d5, d3

// Perform addition with masked p_384. Catch the carry in a, as a bitmask
// for convenience though we only use its LSB below with SHRD

                add     d0, a
                adc     d1, [x+8]
                adc     d2, [x+16]
                adc     d3, [x+24]
                adc     d4, [x+32]
                adc     d5, [x+40]
                sbb     a, a

// Shift right, pushing the carry back down, and store back

                shrd    d0, d1, 1
                mov     [z], d0
                shrd    d1, d2, 1
                mov     [z+8], d1
                shrd    d2, d3, 1
                mov     [z+16], d2
                shrd    d3, d4, 1
                mov     [z+24], d3
                shrd    d4, d5, 1
                mov     [z+32], d4
                shrd    d5, a, 1
                mov     [z+40], d5

// Return

                ret