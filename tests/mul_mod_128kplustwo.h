void bignum_mul_mod_2to130minus1(uint64_t z[3], const uint64_t x[3], const uint64_t y[3]);

// z, x and y must be uint64_t[2k+1]. temp is uint64_t[16*(k+1)].
// two_to_128kplus2_minus1 is uint64_t[2k+1].
// 0 <= *z, *x, *y < 2^(128k+2) - 1
void bignum_mul_mod_2_to_128kplus2_minus1(
    int k, uint64_t *z, uint64_t *x, uint64_t *y, uint64_t *temp,
    uint64_t *two_to_128kplus2_minus1, uint64_t *two_to_64kplus1_plus1,
    uint64_t *two_to_64kplus1_minus1);

void print_bignum(int k, uint64_t *p, const char *c);