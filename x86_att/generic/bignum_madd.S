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
// Multiply-add, z := z + x * y
// Inputs x[m], y[n]; outputs function return (carry-out) and z[k]
//
//    extern uint64_t bignum_madd
//     (uint64_t k, uint64_t *z,
//      uint64_t m, uint64_t *x, uint64_t n, uint64_t *y);
//
// Does the "z := x * y + z" operation, while also returning a "next" or
// "carry" word. In the case where m + n <= p (i.e. the pure product would
// fit in the destination) this is the remainder for the exact result.
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = m, RCX = x, R8 = n, R9 = y,
// returns RAX
// ----------------------------------------------------------------------------


        .globl  bignum_madd
        .text

// These are actually right

#define p %rdi
#define z %rsi
#define n %r8

// These are not

#define c %r15
#define h %r14
#define l %r13
#define x %r12
#define y %r11
#define i %rbx
#define k %r10
#define m %rbp

// These are always local scratch since multiplier result is in these

#define a %rax
#define d %rdx



bignum_madd:

// We use too many registers, and also we need %rax:%rdx for multiplications

        pushq   %rbx
        pushq   %rbp
        pushq   %r12
        pushq   %r13
        pushq   %r14
        pushq   %r15
        movq    %rdx, m

// If the result size is zero, just return %rax = 0
// We could also do this if either input is size 0.

        xorq    %rax, %rax
        testq   p, p
        jz      end

// Set initial 2-part sum to zero (we zero c inside the body)

        xorq    h, h
        xorq    l, l

// Otherwise do outer loop k = 0 ... k = p - 1

        xorq    k, k

outerloop:

// Zero our carry term first; we eventually want it and a zero is useful now
// Set a =  max 0 (k + 1 - n), i = min (k + 1) m
// This defines the range a <= j < i for the inner summation
// Note that since k < p < 2^64 we can assume k + 1 doesn't overflow
// And since we want to increment it anyway, we might as well do it now

        xorq    c, c // c = 0
        incq    k               // k = k + 1

        movq    k, a // a = k + 1
        subq    n, a // a = k + 1 - n
        cmovcq  c, a // a = max 0 (k + 1 - n)

        movq    m, i // i = m
        cmpq    m, k // CF <=> k + 1 < m
        cmovcq  k, i // i = min (k + 1) m

// Turn i into a loop count, and skip things if it's <= 0
// Otherwise set up initial pointers x -> x0[a] and y -> y0[k - a]
// and then launch into the main inner loop, postdecrementing i

        movq    k, d
        subq    i, d
        subq    a, i
        jbe     innerend
        leaq    (%rcx,a,8), x
        leaq    -8(%r9,d,8), y

innerloop:
        movq    (y,i,8), %rax
        mulq      (x)
        addq    $8, x
        addq    %rax, l
        adcq    %rdx, h
        adcq    $0, c
        decq    i
        jnz     innerloop

innerend:

        addq    l, (z)
        adcq    $0, h
        adcq    $0, c
        movq    h, l
        movq    c, h
        addq    $8, z

        cmpq    p, k
        jc      outerloop

// Move the carry term into the return value

        movq    l, %rax

end:
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