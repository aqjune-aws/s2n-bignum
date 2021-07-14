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
// Subtract modulo p_521, z := (x - y) mod p_521
// Inputs x[9], y[9]; output z[9]
//
//    extern void bignum_sub_p521
//     (uint64_t z[static 9], uint64_t x[static 9], uint64_t y[static 9]);
//
// Standard ARM ABI: X0 = z, X1 = x, X2 = y
// ----------------------------------------------------------------------------

#define z x0
#define x x1
#define y x2
#define h x3
#define l x4
#define d0 x5
#define d1 x6
#define d2 x7
#define d3 x8
#define d4 x9
#define d5 x10
#define d6 x11
#define d7 x12
#define d8 x13

.text
.globl bignum_sub_p521

bignum_sub_p521:

// First just subtract the numbers as [d8;d7;d6;d5;d4;d3;d2;d1;d0] = x - y

                ldp     d0, d1, [x]
                ldp     l, h, [y]
                subs    d0, d0, l
                sbcs    d1, d1, h
                ldp     d2, d3, [x, 16]
                ldp     l, h, [y, 16]
                sbcs    d2, d2, l
                sbcs    d3, d3, h
                ldp     d4, d5, [x, 32]
                ldp     l, h, [y, 32]
                sbcs    d4, d4, l
                sbcs    d5, d5, h
                ldp     d6, d7, [x, 48]
                ldp     l, h, [y, 48]
                sbcs    d6, d6, l
                sbcs    d7, d7, h
                ldr     d8, [x, 64]
                ldr     l, [y, 64]
                sbcs    d8, d8, l

// Now if x < y we want (x - y) + p_521 == (x - y) - 1 (mod 2^521)
// Otherwise we just want the existing x - y result. So subtract
// 1 iff the initial subtraction carried, then mask to 521 bits.

                sbcs    d0, d0, xzr
                sbcs    d1, d1, xzr
                sbcs    d2, d2, xzr
                sbcs    d3, d3, xzr
                sbcs    d4, d4, xzr
                sbcs    d5, d5, xzr
                sbcs    d6, d6, xzr
                sbcs    d7, d7, xzr
                sbcs    d8, d8, xzr
                and     d8, d8, 0x1FF

// Store the result

                stp     d0, d1, [z]
                stp     d2, d3, [z, 16]
                stp     d4, d5, [z, 32]
                stp     d6, d7, [z, 48]
                str     d8, [z, 64]

                ret