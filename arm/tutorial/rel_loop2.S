// Unrolled version of rel_loop.S
// Note that the loop counter, x0, is incremented by two
loop:
add x2, x2, #2
add x2, x2, #2
// Ideally, if we have a conditional branch on x0 so that
// it escapes when n is odd, then we can achieve perfect
// program equivalence.

// This can be done by case-splitting n to even or odd before
// starting ENSURES2_WHILE_PAUP_TAC
// BOOL_CASES_TAC? Something like this?
// Since for SHA we have n divided by 5, we will need 5 cases.
// e.g., n = n' * 5 \/ n = n' * 5 + 1 \/ ...
//    or, n = n' * 5 + d, do case analysis on d = 0,1,2,3,4
// This is a bit ugly & symbolic simulation needs to run
// 5 times, but it will work at least

// Actually we can do this case anlysis inside ENSURES2_WHILE_PAUP_TAC
// as well..? But I'm not sure. But it seems it would work. Maybe.

add x0, x0, #2 // unrolled once; x0 is being incremented by 2
cmp x0, x1
bne loop

