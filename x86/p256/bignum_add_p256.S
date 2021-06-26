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
// Add modulo p_256, z := (x + y) mod p_256, assuming x and y reduced
// Inputs x[4], y[4]; output z[4]
//
//    extern void bignum_add_p256
//     (uint64_t z[static 4], uint64_t x[static 4], uint64_t y[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = x, RDX = y
// ----------------------------------------------------------------------------

#define z rdi
#define x rsi
#define y rdx

#define d0 rax
#define d1 rcx
#define d2 r8
#define d3 r9

#define n1 r10
#define n3 rdx
#define c r11

#define n1short r10d

.intel_syntax noprefix

        .globl  bignum_add_p256

bignum_add_p256:

// Load and add the two inputs as 2^256 * c + [d3;d2;d1;d0] = x + y

        xor     c, c
        mov     d0, [x]
        add     d0, [y]
        mov     d1, [x+8]
        adc     d1, [y+8]
        mov     d2, [x+16]
        adc     d2, [y+16]
        mov     d3, [x+24]
        adc     d3, [y+24]
        adc     c, c

// Now subtract 2^256 * c + [d3;d3;d1;d1] = x + y - p_256
// The constants n1 and n3 in [n3; 0; n1; -1] = p_256 are saved for later

        sub     d0, -1
        mov     n1short, 0x00000000ffffffff
        sbb     d1, n1
        sbb     d2, 0
        mov     n3, 0xffffffff00000001
        sbb     d3, n3

// Since by hypothesis x < p_256 we know x + y - p_256 < 2^256, so the top
// carry c actually gives us a bitmask for x + y - p_256 < 0, which we
// now use to make a masked p_256' = [n3; 0; n1; c]

        sbb     c, 0
        and     n1, c
        and     n3, c

// Do the corrective addition and copy to output

        add     d0, c
        mov     [z], d0
        adc     d1, n1
        mov     [z+8], d1
        adc     d2, 0
        mov     [z+16], d2
        adc     d3, n3
        mov     [z+24], d3

        ret