// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Reduce modulo group order, z := x mod n_384
// Input x[k]; output z[6]
//
//    extern void bignum_mod_n384(uint64_t z[static 6], uint64_t k,
//                                const uint64_t *x);
//
// Reduction is modulo the group order of the NIST curve P-384.
//
// Standard x86-64 ABI: RDI = z, RSI = k, RDX = x
// Microsoft x64 ABI:   RCX = z, RDX = k, R8 = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_mod_n384)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_mod_n384)
        .text

#define z rdi
#define k rsi
#define x rcx

#define m0 r8
#define m1 r9
#define m2 r10
#define m3 r11
#define m4 r12
#define m5 r13
#define d r14

#define n0 rax
#define n1 rbx
#define n2 rdx
#define q rdx

#define n0short eax
#define qshort edx


S2N_BN_SYMBOL(bignum_mod_n384):
        _CET_ENDBR

#if WINDOWS_ABI
        push    rdi
        push    rsi
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

// Save extra registers

        push    rbx
        push    r12
        push    r13
        push    r14

// If the input is already <= 5 words long, go to a trivial "copy" path

        cmp     k, 6
        jc      bignum_mod_n384_shortinput

// Otherwise load the top 6 digits (top-down) and reduce k by 6

        sub     k, 6
        mov     m5, [rdx+8*k+40]
        mov     m4, [rdx+8*k+32]
        mov     m3, [rdx+8*k+24]
        mov     m2, [rdx+8*k+16]
        mov     m1, [rdx+8*k+8]
        mov     m0, [rdx+8*k]

// Move x into another register to leave rdx free for multiplies and use of n2

        mov     x, rdx

// Reduce the top 6 digits mod n_384 (a conditional subtraction of n_384)

        mov     n0, 0x1313e695333ad68d
        mov     n1, 0xa7e5f24db74f5885
        mov     n2, 0x389cb27e0bc8d220

        add     m0, n0
        adc     m1, n1
        adc     m2, n2
        adc     m3, 0
        adc     m4, 0
        adc     m5, 0
        sbb     d, d
        not     d
        and     n0, d
        and     n1, d
        and     n2, d
        sub     m0, n0
        sbb     m1, n1
        sbb     m2, n2
        sbb     m3, 0
        sbb     m4, 0
        sbb     m5, 0

// Now do (k-6) iterations of 7->6 word modular reduction

        test    k, k
        jz      bignum_mod_n384_writeback

bignum_mod_n384_loop:

// Compute q = min (m5 + 1) (2^64 - 1)

        mov     qshort, 1
        add     q, m5
        sbb     d, d
        or      q, d

// Load the next digit so current m to reduce = [m5;m4;m3;m2;m1;m0;d]

        mov     d, [x+8*k-8]

// Now form [m5;m4;m3;m2;m1;m0;d] = m - q * n_384

        sub     m5, q
        xor     n0, n0
        mov     n0, 0x1313e695333ad68d
        mulx    n1, n0, n0
        adcx    d, n0
        adox    m0, n1
        mov     n0,0xa7e5f24db74f5885
        mulx    n1, n0, n0
        adcx    m0, n0
        adox    m1, n1
        mov     n0, 0x389cb27e0bc8d220
        mulx    n1, n0, n0
        adcx    m1, n0
        mov     n0short, 0
        adox    n1, n0
        adcx    m2, n1
        adc     m3, 0
        adc     m4, 0
        adc     m5, 0

// Now our top word m5 is either zero or all 1s. Use it for a masked
// addition of n_384, which we can do by a *subtraction* of
// 2^384 - n_384 from our portion

        mov     n0, 0x1313e695333ad68d
        and     n0, m5
        mov     n1, 0xa7e5f24db74f5885
        and     n1, m5
        mov     n2, 0x389cb27e0bc8d220
        and     n2, m5

        sub     d, n0
        sbb     m0, n1
        sbb     m1, n2
        sbb     m2, 0
        sbb     m3, 0
        sbb     m4, 0

// Now shuffle registers up and loop

        mov     m5, m4
        mov     m4, m3
        mov     m3, m2
        mov     m2, m1
        mov     m1, m0
        mov     m0, d

        dec     k
        jnz     bignum_mod_n384_loop

// Write back

bignum_mod_n384_writeback:

        mov     [z], m0
        mov     [z+8], m1
        mov     [z+16], m2
        mov     [z+24], m3
        mov     [z+32], m4
        mov     [z+40], m5

// Restore registers and return

        pop     r14
        pop     r13
        pop     r12
        pop     rbx
#if WINDOWS_ABI
        pop    rsi
        pop    rdi
#endif
        ret

bignum_mod_n384_shortinput:

        xor     m0, m0
        xor     m1, m1
        xor     m2, m2
        xor     m3, m3
        xor     m4, m4
        xor     m5, m5

        test    k, k
        jz      bignum_mod_n384_writeback
        mov     m0, [rdx]
        dec     k
        jz      bignum_mod_n384_writeback
        mov     m1, [rdx + 8]
        dec     k
        jz      bignum_mod_n384_writeback
        mov     m2, [rdx + 16]
        dec     k
        jz      bignum_mod_n384_writeback
        mov     m3, [rdx + 24]
        dec     k
        jz      bignum_mod_n384_writeback
        mov     m4, [rdx + 32]
        jmp     bignum_mod_n384_writeback

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
