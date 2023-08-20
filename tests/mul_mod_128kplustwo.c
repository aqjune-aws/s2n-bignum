#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <inttypes.h>

#include "../include/s2n-bignum.h"

//#define ASSERT(x) assert(x)
#define ASSERT(x)

static inline uint64_t addcarry64_overflows(uint64_t x, uint64_t y, uint64_t carry) {
  ASSERT(carry <= 1);
  uint64_t m = -1ull - carry;
  return (m < x) | (m - x < y);
}

static inline uint64_t add64_overflows(uint64_t x, uint64_t y) {
  uint64_t m = -1ull;
  return m - x < y;
}

// x - y - carry underflows?
static inline uint64_t subcarry64_underflows(uint64_t x, uint64_t y, uint64_t carry) {
  return ((y == -1ull) & (carry == 1)) | (x < y + carry);
}

static inline uint64_t sub64_underflows(uint64_t x, uint64_t y) {
  return x < y;
}

static inline uint64_t lt_u65(uint64_t xh, uint64_t xl, uint64_t yh, uint64_t yl) {
  return (xh < yh) | ((xh == yh) & (xl < yl));
}

// Adds two 65-bit integers x and y.
// Actually, this is simply 128 bit int add.
static inline void add_u65(
    uint64_t *zh, uint64_t *zl,
    uint64_t xh, uint64_t xl,
    uint64_t yh, uint64_t yl) {
  *zl = xl + yl;
  *zh = xh + yh + add64_overflows(xl, yl);
}

// Adds two 130-bit integers.
// Actually, this is simply 192 bit int add.
static inline void add_u130(
    uint64_t *z2, uint64_t *z1, uint64_t *z0,
    uint64_t x2, uint64_t x1, uint64_t x0,
    uint64_t y2, uint64_t y1, uint64_t y0) {
  uint64_t carry1 = add64_overflows(x0, y0);
  *z0 = x0 + y0;
  uint64_t carry2 = addcarry64_overflows(x1, y1, carry1);
  *z1 = x1 + y1 + carry1;
  *z2 = x2 + y2 + carry2;
}

static inline uint64_t add_u192(
    uint64_t *z2, uint64_t *z1, uint64_t *z0,
    uint64_t x2, uint64_t x1, uint64_t x0,
    uint64_t y2, uint64_t y1, uint64_t y0) {
  uint64_t carry1 = add64_overflows(x0, y0);
  *z0 = x0 + y0;
  uint64_t carry2 = addcarry64_overflows(x1, y1, carry1);
  *z1 = x1 + y1 + carry1;
  uint64_t carry3 = addcarry64_overflows(x2, y2, carry2);
  *z2 = x2 + y2 + carry2;
  return carry3;
}

static inline uint64_t add_u256(
    uint64_t *z4, uint64_t *z3, uint64_t *z2, uint64_t *z1, uint64_t *z0,
    uint64_t x4, uint64_t x3, uint64_t x2, uint64_t x1, uint64_t x0,
    uint64_t y4, uint64_t y3, uint64_t y2, uint64_t y1, uint64_t y0) {
  uint64_t carry1 = add64_overflows(x0, y0);
  *z0 = x0 + y0;
  uint64_t carry2 = addcarry64_overflows(x1, y1, carry1);
  *z1 = x1 + y1 + carry1;
  uint64_t carry3 = addcarry64_overflows(x2, y2, carry2);
  *z2 = x2 + y2 + carry2;
  uint64_t carry4 = addcarry64_overflows(x3, y3, carry3);
  *z3 = x3 + y3 + carry3;
  uint64_t carry5 = addcarry64_overflows(x4, y4, carry4);
  *z4 = x4 + y4 + carry4;
  return carry5;
}

static inline void addcarry_u256(uint64_t z[5], uint64_t carry) {
  add_u256(&z[4], &z[3], &z[2], &z[1], &z[0],
      z[4], z[3], z[2], z[1], z[0],
      0, 0, 0, 0, carry);
}

// Performs u65 - u65 -> u65(!)
// Assumes that xh:xl >= yh:yl.
static inline void sub_u65(uint64_t *zh, uint64_t *zl, uint64_t xh, uint64_t xl, uint64_t yh, uint64_t yl) {
  *zl = xl - yl;
  *zh = xh - yh - (xl < yl ? 1 : 0);
}

// Performs 130 bit x - y, and returns carry.
// Actually, this is simply 192 bit int sub.
static inline uint64_t sub_u130(
    uint64_t *z2, uint64_t *z1, uint64_t *z0,
    uint64_t x2, uint64_t x1, uint64_t x0,
    uint64_t y2, uint64_t y1, uint64_t y0) {
  uint64_t carry1 = sub64_underflows(x0, y0);
  *z0 = x0 - y0;
  uint64_t carry2 = subcarry64_underflows(x1, y1, carry1);
  *z1 = x1 - y1 - carry1;
  uint64_t carry3 = subcarry64_underflows(x2, y2, carry2);
  *z2 = x2 - y2 - carry2;
  return carry3;
}

static inline uint64_t sub_u256(
    uint64_t *z4, uint64_t *z3, uint64_t *z2, uint64_t *z1, uint64_t *z0,
    uint64_t x4, uint64_t x3, uint64_t x2, uint64_t x1, uint64_t x0,
    uint64_t y4, uint64_t y3, uint64_t y2, uint64_t y1, uint64_t y0) {
  uint64_t carry1 = sub64_underflows(x0, y0);
  *z0 = x0 - y0;
  uint64_t carry2 = subcarry64_underflows(x1, y1, carry1);
  *z1 = x1 - y1 - carry1;
  uint64_t carry3 = subcarry64_underflows(x2, y2, carry2);
  *z2 = x2 - y2 - carry2;
  uint64_t carry4 = subcarry64_underflows(x3, y3, carry3);
  *z3 = x3 - y3 - carry3;
  uint64_t carry5 = subcarry64_underflows(x4, y4, carry4);
  *z4 = x4 - y4 - carry4;
  return carry5;
}

static inline void subcarry_u256(uint64_t z[5], uint64_t carry) {
  sub_u256(&z[4], &z[3], &z[2], &z[1], &z[0],
      z[4], z[3], z[2], z[1], z[0],
      0, 0, 0, 0, carry);
}

static inline uint64_t umulh_u64(uint64_t a, uint64_t b) {
  __uint128_t a128 = a, b128 = b;
  return (uint64_t)((a128 * b128) >> 64);
}

// If x_u65 is true, xh::xl is considered as 65-bit int. If false, it is 66-bit int.
static inline void mul_u66_u66_general(uint64_t *z2, uint64_t *z1, uint64_t *z0,
      uint64_t xh, uint64_t xl, uint64_t yh, uint64_t yl,
      int x_u65, int y_u65) {
  *z0 = xl * yl;
  *z1 = umulh_u64(xl, yl);
  *z2 = 0;
  // xl * yh
  if (y_u65) {
    if (yh) {
      *z2 += add64_overflows(*z1, xl);
      *z1 += xl;
    }
  } else {
    if (yh & 1) {
      *z2 += add64_overflows(*z1, xl);
      *z1 += xl;
    }
    if (yh & 2) {
      uint64_t xl2 = xl << 1;
      *z2 += add64_overflows(*z1, xl2);
      *z1 += xl2;
      *z2 += (xl >> 63);
    }
  }
  // xh * yl
  if (x_u65) {
    if (xh) {
      *z2 += add64_overflows(*z1, yl);
      *z1 += yl;
    }
  } else {
    if (xh & 1) {
      *z2 += add64_overflows(*z1, yl);
      *z1 += yl;
    }
    if (xh & 2) {
      uint64_t yl2 = yl << 1;
      *z2 += add64_overflows(*z1, yl2);
      *z1 += yl2;
      *z2 += (yl >> 63);
    }
  }
  // xh * yh
  if (y_u65)
    *z2 += yh ? xh : 0;
  else {
    *z2 += (yh & 1) ? xh : 0;
    *z2 += (yh & 2) ? (xh << 1) : 0;
  }
}

static inline void mul_u66_u66(uint64_t *z2, uint64_t *z1, uint64_t *z0,
      uint64_t xh, uint64_t xl, uint64_t yh, uint64_t yl) {
  ASSERT(xh < 4);
  ASSERT(yh < 4);
  mul_u66_u66_general(z2, z1, z0, xh, xl, yh, yl, 0, 0);
}

static inline void mul_u65_u65(uint64_t *z2, uint64_t *z1, uint64_t *z0,
      uint64_t xh, uint64_t xl, uint64_t yh, uint64_t yl) {
  ASSERT(xh < 2);
  ASSERT(yh < 2);
  mul_u66_u66_general(z2, z1, z0, xh, xl, yh, yl, 1, 1);
}

// Given x, y < 2^130-1, evaluate (x*y) % (2^130-1).
void bignum_mul_mod_2to130minus1(uint64_t z[3], const uint64_t x[3], const uint64_t y[3]) {
  // l = 128
  // x = 2^65 xh + xl
  // y = 2^65 yh + yl
  // x * y =    ((xh+xl)(yh+yl) + (xh-xl)(yh-yl))/2      // (xhyh+xlyl)
  //          + ((xh+xl)(yh+yl) - (xh-xl)(yh-yl))/2*2^65 // (xhyl+xlyh)
  //          + (2^130-1)xhyh
  //       \equiv
  //          ((xh+xl)(yh+yl) + (xh-xl)(yh-yl))/2 + ((xh+xl)(yh+yl) - (xh-xl)(yh-yl))/2*2^65
  //            mod 2^130 - 1
  uint64_t xh1 = x[2] >> 1, xh0 = (x[2] << 63) | (x[1] >> 1);
  uint64_t xl1 = x[1] & 1,  xl0 = x[0];
  uint64_t yh1 = y[2] >> 1, yh0 = (y[2] << 63) | (y[1] >> 1);
  uint64_t yl1 = y[1] & 1,  yl0 = y[0];

  // xhpl = xh+xl
  // yhpl = yh+yl
  uint64_t xhpl_h, xhpl_l, yhpl_h, yhpl_l;
  add_u65(&xhpl_h, &xhpl_l, xh1, xh0, xl1, xl0);
  add_u65(&yhpl_h, &yhpl_l, yh1, yh0, yl1, yl0);

  // xhml = |xh-xl|, xhml_sgn = xh < xl
  // yhml = |yh-yl|, yhml_sgn = yh < yl
  uint64_t xhml_sgn = lt_u65(xh1, xh0, xl1, xl0);
  uint64_t xhml_sgn_mask = -xhml_sgn;
  uint64_t xhml_h, xhml_l;
  sub_u65(&xhml_h, &xhml_l, xh1, xh0, xl1, xl0);
  // If xhml_sgn is true, negate the subtraction to make it an absolute value.
  xhml_h ^= xhml_sgn_mask;
  xhml_l ^= xhml_sgn_mask;
  add_u65(&xhml_h, &xhml_l, xhml_h, xhml_l, 0, xhml_sgn);

  uint64_t yhml_sgn = lt_u65(yh1, yh0, yl1, yl0);
  uint64_t yhml_sgn_mask = -yhml_sgn;
  uint64_t yhml_h, yhml_l;
  sub_u65(&yhml_h, &yhml_l, yh1, yh0, yl1, yl0);
  // If yhml_sgn is true, negate the subtraction to make it an absolute value.
  yhml_h ^= yhml_sgn_mask;
  yhml_l ^= yhml_sgn_mask;
  add_u65(&yhml_h, &yhml_l, yhml_h, yhml_l, 0, yhml_sgn);

  uint64_t t0, t1, t2, s0, s1, s2;
  // (xh+xl)(yh+yl)
  mul_u66_u66(&t2, &t1, &t0, xhpl_h, xhpl_l, yhpl_h, yhpl_l);
  // |xh-xl||yh-yl|
  mul_u65_u65(&s2, &s1, &s0, xhml_h, xhml_l, yhml_h, yhml_l);
  // sign of (xh-xl)(yh-yl)
  uint64_t sgn = xhml_sgn ^ yhml_sgn;
  uint64_t sgn_mask = xhml_sgn_mask ^ yhml_sgn_mask;

  // temp stores (2^130-1)^2 ~= 2^260, requiring 5 words
  uint64_t mulres[5] = {0,0,0,0,0};

  // ((xh+xl)(yh+yl) + sgn * |xh-xl||yh-yl|)/2
  uint64_t ss2 = s2 ^ sgn_mask, ss1 = s1 ^ sgn_mask, ss0 = s0 ^ sgn_mask;
  add_u256(&mulres[4], &mulres[3], &mulres[2], &mulres[1], &mulres[0],
           0, 0, t2, t1, t0, sgn_mask, sgn_mask, ss2, ss1, ss0);
  addcarry_u256(mulres, sgn);
  ASSERT((mulres[0] & 1) == 0);
  mulres[0] = (mulres[0] >> 1) | (mulres[1] << 63);
  mulres[1] = (mulres[1] >> 1) | (mulres[2] << 63);
  mulres[2] = (mulres[2] >> 1) | (mulres[3] << 63);
  // mulres[3], mulres[4] don't need shifts because they are either -1 or 0

  // q = ((xh+xl)(yh+yl) - sgn * |xh-xl||yh-yl|)/2*2^65
  //   = ((xh+xl)(yh+yl) - sgn * |xh-xl||yh-yl|)*2^64
  uint64_t q[5];
  // Actually, the most significant 64 bits are not necessary.
  sub_u256(&q[4], &q[3], &q[2], &q[1], &q[0],
      0, 0, t2, t1, t0, sgn_mask, sgn_mask, ss2, ss1, ss0);
  subcarry_u256(q, sgn);

  // Now do ... + q * 2^64
  uint64_t carry1 = add64_overflows(mulres[1], q[0]);
  mulres[1] += q[0];
  uint64_t carry2 = addcarry64_overflows(mulres[2], q[1], carry1);
  mulres[2] += q[1] + carry1;
  uint64_t carry3 = addcarry64_overflows(mulres[3], q[2], carry2);
  mulres[3] += q[2] + carry2;
  mulres[4] += q[3] + carry3;

  uint64_t prime[5] = {-1ull, -1ull, 3, 0, 0};

  // Calculate mulres mod 2^130 - 1.
  // if mulres = k0 + k1*2^130,
  // mulres mod 2^130 - 1 = k0 + k1 mod 2^130-1
  s0 = mulres[0];
  s1 = mulres[1];
  s2 = mulres[2] & 3;
  t0 = (mulres[2] >> 2) | (mulres[3] << 62);
  t1 = (mulres[3] >> 2) | (mulres[4] << 62);
  t2 = mulres[4] >> 2;
  add_u130(&z[2], &z[1], &z[0], s2, s1, s0, t2, t1, t0);
  
  // Conditionally subtract 2^130 - 1
  uint64_t cond = bignum_ge(3, z, 3, prime);
  bignum_optsub(3, z, z, cond, prime);
}

void print_bignum(int k, uint64_t *p, const char *c) {
  printf("%s: [", c);
  for (int i = 0; i + 1 < k; ++i)
    printf("%lu, ", p[i]);
  printf("%lu]\n", p[k-1]);
}

static inline void mul_64kplusone(int k, uint64_t *z, uint64_t *x, uint64_t *y) {
  uint64_t buf[96];
  if (k == 8)
    bignum_mul_8_16_neon(z, x, y);
  else if (k == 16)
    bignum_kmul_16_32_neon(z, x, y, buf);
  else if (k == 32)
    bignum_kmul_32_64_neon(z, x, y, buf);
  else
    bignum_mul(2*k, z, k, x, k, y);

  uint64_t xmsb = x[k], ymsb = y[k];
  ASSERT(xmsb < 2);
  ASSERT(ymsb < 2);
  uint64_t c = bignum_optadd(k, z+k, z+k, xmsb, y);
  z[2 * k] = c;
  c = bignum_optadd(k, z+k, z+k, ymsb, x);
  z[2 * k] += c;
  z[2 * k] += xmsb & ymsb;
}

// x and y: uint64_t[k+1]
// z: uint64_t[2k+1]
// tempbuf: uint64_t[k+1]
static inline void mul_64kplustwo(int k, uint64_t *z, uint64_t *x, uint64_t *y, uint64_t *_x) {
  uint64_t buf[96];
  if (k == 8)
    bignum_mul_8_16_neon(z, x, y);
  else if (k == 16)
    bignum_kmul_16_32_neon(z, x, y, buf);
  else if (k == 32)
    bignum_kmul_32_64_neon(z, x, y, buf);
  else
    bignum_mul(2*k, z, k, x, k, y);

  uint64_t xmsb = x[k], ymsb = y[k];
  ASSERT(xmsb < 4);
  ASSERT(ymsb < 4);
  uint64_t c = bignum_optadd(k, z+k, z+k, xmsb&1, y);
  z[2 * k] = c;
  c = bignum_optadd(k, z+k, z+k, ymsb&1, x);
  z[2 * k] += c;

  uint64_t tempbuf[1024];
  tempbuf[0] = x[0] << 1;
  for (int i = 1; i < k; ++i)
    tempbuf[i] = (x[i] << 1) | (x[i-1] >> 63);
  c = bignum_optadd(k, z+k, z+k, ymsb&2, tempbuf);
  z[2 * k] += c + (ymsb&2 ? (x[k-1] >> 63) : 0);

  tempbuf[0] = y[0] << 1;
  for (int i = 1; i < k; ++i)
    tempbuf[i] = (y[i] << 1) | (y[i-1] >> 63);
  c = bignum_optadd(k, z+k, z+k, xmsb&2, tempbuf);
  z[2 * k] += c + (xmsb&2 ? (y[k-1] >> 63) : 0);

  z[2 * k] += xmsb * ymsb; // Can be even cheaper!
}

/*
// z, x and y must be uint64_t[2k+1]. temp is uint64_t[16*(k+1)].
// two_to_128kplus2_minus1 is uint64_t[2k+1].
// 0 <= *z, *x, *y < 2^(128k+2) - 1
void bignum_mul_mod_2_to_128kplus2_minus1(
    int k, uint64_t *z, const uint64_t *x, const uint64_t *y, uint64_t *temp,
    uint64_t *two_to_128kplus2_minus1) {
  // x = 2^(64k+1) xh + xl
  // y = 2^(64k+1) yh + yl
  // x * y =    ((xh+xl)(yh+yl) + (xh-xl)(yh-yl))/2      // (xhyh+xlyl)
  //          + ((xh+xl)(yh+yl) - (xh-xl)(yh-yl))/2*2^(64k+1) // (xhyl+xlyh)
  //          + (2^(128k+2)-1)xhyh
  //       \equiv
  //          ((xh+xl)(yh+yl) + (xh-xl)(yh-yl))/2 + ((xh+xl)(yh+yl) - (xh-xl)(yh-yl))*2^64k
  //            mod 2^(128k) - 1
  uint64_t *xl = temp;
  uint64_t *xh = temp + (k + 1);
  uint64_t *yl = temp + 2 * (k + 1);
  uint64_t *yh = temp + 3 * (k + 1);
  for (int i = 0; i < k; ++i) {
    xl[i] = x[i];
    yl[i] = y[i];
    xh[i] = (x[k + i] >> 1) | (x[k + i + 1] << 63);
    yh[i] = (y[k + i] >> 1) | (y[k + i + 1] << 63);
  }
  xl[k] = x[k] & 1;
  xh[k] = x[2 * k] >> 1;
  yl[k] = y[k] & 1;
  yh[k] = y[2 * k] >> 1;

  // xhpl = xh+xl
  // yhpl = yh+yl
  uint64_t *xhpl = temp + 4 * (k + 1);
  uint64_t *yhpl = temp + 5 * (k + 1);
  bignum_add(k+1, xhpl, k+1, xh, k+1, xl);
  bignum_add(k+1, yhpl, k+1, yh, k+1, yl);

  // xhml = |xh-xl|, xhml_sgn = xh < xl
  // yhml = |yh-yl|, yhml_sgn = yh < yl
  uint64_t *xhml = temp + 6 * (k + 1);
  uint64_t xhml_sgn = bignum_lt(k + 1, xh, k + 1, xl);
  bignum_sub(k + 1, xhml, k + 1, xh, k + 1, xl);
  // If xhml_sgn is true, negate the subtraction to make it an absolute value.
  bignum_optneg(k + 1, xhml, xhml_sgn, xhml);

  uint64_t *yhml = temp + 7 * (k + 1);
  uint64_t yhml_sgn = bignum_lt(k + 1, yh, k + 1, yl);
  bignum_sub(k + 1, yhml, k + 1, yh, k + 1, yl);
  // If yhml_sgn is true, negate the subtraction to make it an absolute value.
  bignum_optneg(k + 1, yhml, yhml_sgn, yhml);

  // (xh+xl)(yh+yl)
  // 2 * k + 1 is enough, but use 4 * k + 1. Top 2*k words are zero.
  uint64_t *t = temp;
  mul_64kplustwo(k, t, xhpl, yhpl, temp + 8 * (k + 1));
  //bignum_mul(2 * k + 1, t, k + 1, xhpl, k + 1, yhpl);
  for (int i = 2 * k + 1; i < 4 * k + 1; ++i)
    t[i] = 0;

  // |xh-xl||yh-yl|; uses 4 * k + 1 words. Upper 2*k words are zero.
  uint64_t *s = temp + 8 * (k + 1);
  //bignum_mul(2 * k + 1, s, k + 1, xhml, k + 1, yhml);
  mul_64kplusone(k, s, xhml, yhml);
  for(int i = 2 * k + 1; i < 4 * k + 1; ++i)
    s[i] = 0;
  // sign of (xh-xl)(yh-yl)
  uint64_t sgn = xhml_sgn ^ yhml_sgn;

  // mulres stores (2^(128k+2)-1)^2 ~= 2^(256k+4) = 4k+1 words.
  uint64_t *mulres = temp + 4 * (k + 1);
  uint64_t *q = temp + 12 * (k + 1);

  // ((xh+xl)(yh+yl) + sgn * |xh-xl||yh-yl|)/2
  bignum_optneg(4 * k + 1, q, sgn, s);
  bignum_add(4 * k + 1, mulres, 4 * k + 1, t, 4 * k + 1, q);
  ASSERT((mulres[0] & 1) == 0);
  // divide by two
  for (int i = 0; i < 2 * k + 1; ++i)
    mulres[i] = (mulres[i] >> 1) | (mulres[i + 1] << 63);
  // mulres[2k + 1... 4k] don't need shifts because they are either -1 or 0

  // q = ((xh+xl)(yh+yl) - sgn * |xh-xl||yh-yl|)/2*2^(64k+1)
  //   = ((xh+xl)(yh+yl) - sgn * |xh-xl||yh-yl|)*2^(64k)
  bignum_sub(4 * k + 1, q, 4 * k + 1, t, 4 * k + 1, q);

  // .. + q * 2^(64k)
  bignum_add(3 * k + 1, mulres + k,
             3 * k + 1, mulres + k,
             3 * k + 1, q);

  // Calculate mulres mod 2^(128k+2) - 1.
  // if mulres = k0 + k1*2^(128k+2),
  // mulres mod 2^(128k+2) - 1 = k0 + k1 mod 2^(128k+2)-1
  uint64_t *low = temp, *high = temp + 2 * (k + 1);
  for (int i = 0; i < 2*k; ++i) {
    low[i] = mulres[i];
    high[i] = (mulres[i + 2 * k] >> 2) | (mulres[i + 2 * k + 1] << 62);
  }
  low[2 * k] = mulres[2 * k] & 3;
  high[2 * k] = mulres[4 * k] >> 2;
  bignum_add(2 * k + 1, z, 2 * k + 1, low, 2 * k + 1, high);
  
  // Conditionally subtract 2^(128k+2) - 1
  uint64_t cond = bignum_ge(2 * k + 1, z, 2 * k + 1, two_to_128kplus2_minus1);
  bignum_optsub(2 * k + 1, z, z, cond, two_to_128kplus2_minus1);
}
*/


static void copy_hilo(uint64_t *xh, uint64_t *xl, int k, const uint64_t *x) {
  for (int i = 0; i < k; ++i) {
    xl[i] = x[i];
    xh[i] = (x[k + i] >> 1) | (x[k + i + 1] << 63);
  }
  xl[k] = x[k] & 1;
  xh[k] = x[2 * k] >> 1;
}

// Given t: 2k+1 words, calculate t mod 2^{64k+1}+1 and store at t.
// temp must be 2k+2 words.
// If t = t_h * 2^{64k+1} + t_l,
//    t mod (2^{64k+1}+1) = (t_l - t_h) mod (2^{64k+1}+1)
static void mod_2_to_64kplus1_plus1(int k, uint64_t *t, uint64_t *temp, uint64_t *two_to_64kplus1_plus1) {
  uint64_t *t_hi = temp;
  uint64_t *t_lo = temp + (k + 1);
  copy_hilo(t_hi, t_lo, k, t);

  uint64_t overflow = bignum_sub(k+1, t, k+1, t_lo, k+1, t_hi);
  bignum_optadd(k+1, t, t, overflow, two_to_64kplus1_plus1);
}

// Given t: 2k+1 words, calculate t mod 2^{64k+1}-1 and store at t.
// temp must be 2k+2 words.
// If t = t_h * 2^{64k+1} + t_l,
//    t mod (2^{64k+1}-1) = (t_h + t_l) mod (2^{64k+1}-1)
static void mod_2_to_64kplus1_minus1(
    int k, uint64_t *t, uint64_t *temp, uint64_t *two_to_64kplus1_minus1) {
  uint64_t *t_hi = temp;
  uint64_t *t_lo = temp + (k + 1);
  copy_hilo(t_hi, t_lo, k, t);

  bignum_add(k+1, t, k+1, t_lo, k+1, t_hi);
  uint64_t cmp = bignum_ge(k+1, t, k+1, two_to_64kplus1_minus1);
  bignum_optsub(k+1, t, t, cmp, two_to_64kplus1_minus1);
  cmp = bignum_ge(k+1, t, k+1, two_to_64kplus1_minus1);
  bignum_optsub(k+1, t, t, cmp, two_to_64kplus1_minus1);
}

// Given t: k+1 words and t < 2*2^{64k+1}, calculate t mod 2^{64k+1}-1 and store at t.
// If t = t_h * 2^{64k+1} + t_l,
//    t mod (2^{64k+1}-1) = (t_h + t_l) mod (2^{64k+1}-1)
static void mod_2_to_64kplus1_minus1_short(
    int k, uint64_t *t, uint64_t *temp, uint64_t *two_to_64kplus1_minus1) {
  uint64_t t_hi = t[k] >> 1;
  t[k] &= 1;

  bignum_add(k+1, t, k+1, t, 1, &t_hi);
  uint64_t cmp = bignum_ge(k+1, t, k+1, two_to_64kplus1_minus1);
  bignum_optsub(k+1, t, t, cmp, two_to_64kplus1_minus1);
}

void bignum_mul_mod_2_to_128kplus2_minus1(
    int k, uint64_t *z, uint64_t *x, uint64_t *y, uint64_t *temp,
    uint64_t *two_to_128kplus2_minus1, uint64_t *two_to_64kplus1_plus1,
    uint64_t *two_to_64kplus1_minus1) {
  //print_bignum(2*k+1, x, "x");
  //print_bignum(2*k+1, y, "y");
  //print_bignum(2*k+1, two_to_128kplus2_minus1, "modulus");
  //print_bignum(k+1, two_to_64kplus1_plus1, "modulus_half_plusone");
  //print_bignum(k+1, two_to_64kplus1_minus1, "modulus_half_minusone");

  // x = 2^(64k+1) xh + xl
  // y = 2^(64k+1) yh + yl
  uint64_t *xl = temp;
  uint64_t *xh = temp + (k + 1);
  uint64_t *yl = temp + 2 * (k + 1);
  uint64_t *yh = temp + 3 * (k + 1);
  copy_hilo(xh, xl, k, x);
  copy_hilo(yh, yl, k, y);

  //print_bignum(k+1, xh, "xh");
  //print_bignum(k+1, xl, "xl");
  //print_bignum(k+1, yh, "yh");
  //print_bignum(k+1, yl, "yl");

  // xhpl = xh+xl
  // yhpl = yh+yl
  uint64_t *xhpl = temp + 4 * (k + 1);
  uint64_t *yhpl = temp + 5 * (k + 1);
  bignum_add(k+1, xhpl, k+1, xh, k+1, xl);
  bignum_add(k+1, yhpl, k+1, yh, k+1, yl);

  // xhml = |xh-xl|, xhml_sgn = xh < xl
  // yhml = |yh-yl|, yhml_sgn = yh < yl
  uint64_t *xhml = temp + 6 * (k + 1);
  uint64_t xhml_sgn = bignum_sub(k + 1, xhml, k + 1, xh, k + 1, xl);
  // If xhml_sgn is true, negate the subtraction to make it an absolute value.
  bignum_optneg(k + 1, xhml, xhml_sgn, xhml);
  //print_bignum(k+1, xhml, "|xh-xl|");

  uint64_t *yhml = temp + 7 * (k + 1);
  uint64_t yhml_sgn = bignum_sub(k + 1, yhml, k + 1, yh, k + 1, yl);
  // If yhml_sgn is true, negate the subtraction to make it an absolute value.
  bignum_optneg(k + 1, yhml, yhml_sgn, yhml);
  //print_bignum(k+1, yhml, "|yh-yl|");
  //printf("xhml_sgn: %lu, yhml_sgn: %lu\n", xhml_sgn, yhml_sgn);

  // 1. |xh-xl|*|yh-yl| mod (2^(64k+1)+1)
  //    First, do |xh-xl|*|yh-yl|
  uint64_t *t = z;
  mul_64kplusone(k, t, xhml, yhml);
  //print_bignum(2*k+1, t, "|xh-xl|*|yh-yl|");

  //    Second, do .. mod (2^(64k+1)+1).
  mod_2_to_64kplus1_plus1(k, t, temp + 8 * (k+1), two_to_64kplus1_plus1);
  //print_bignum(k+1, t, "|t|=|xh-xl|*|yh-yl| mod (2^(64k+1)+1)");
  bignum_modoptneg(k+1, t, yhml_sgn^xhml_sgn, t, two_to_64kplus1_plus1);
  //print_bignum(k+1, t, "t=(xh-xl)*(yh-yl) mod (2^(64k+1)+1)");

  // 2. (xh+xl)(yh+yl) mod (2^(64k+1)-1)
  //    First, do xh+xl mod (2^(64k+1)-1) and yh+yl mod (2^(64k+1)-1)
  //print_bignum(k+1, xhpl, "xh+xl");
  mod_2_to_64kplus1_minus1_short(k, xhpl, temp + 8 * (k+1), two_to_64kplus1_minus1);
  //print_bignum(k+1, xhpl, "(xh+xl) mod R1");
  //print_bignum(k+1, yhpl, "yh+yl");
  mod_2_to_64kplus1_minus1_short(k, yhpl, temp + 8 * (k+1), two_to_64kplus1_minus1);
  //print_bignum(k+1, yhpl, "(yh+yl) mod R1");

  //    Second, do ((xh+xl) mod (2^(64k+1)-1)) * ((yh+yl) mod (2^(64k+1)-1))
  uint64_t *s = temp + 2 * (k + 1);
  mul_64kplusone(k, s, xhpl, yhpl);
  //print_bignum(2*k+1, s, "(yh+yl) mod R1 * (xh+xl) mod R1");

  //    Finally, do .. mod (2^(64k+1)-1)
  mod_2_to_64kplus1_minus1(k, s, temp + 8 * (k+1), two_to_64kplus1_minus1);
  //print_bignum(k+1, s, "s");

  // Now, from s and t, reconstruct the answer.
  // t + (2^{64k+1}+1) * (2^{64k} * (s-t) mod (2^{64k+1}-1))
  // (s-t) mod (2^{64k+1}-1)
  uint64_t *smt = temp + 9 * (k+1);
  uint64_t carry = bignum_sub(k+1, smt, k+1, s, k+1, t);
  bignum_optadd(k+1, smt, smt, carry, two_to_64kplus1_minus1);
  //print_bignum(k+1,smt,"(s-t) mod (2^{64k+1}-1)");

  // (2^{64k} * (s-t) mod (2^{64k+1}-1))
  uint64_t smt_lsb = smt[0] & 1;
  for (int i = 0; i < k; ++i)
    smt[i] = (smt[i] >> 1) | (smt[i+1] << 63);
  smt[k] = smt[k] >> 1;
  bignum_add(1, smt+k, 1, smt+k, 1, &smt_lsb);
  //print_bignum(k+1,smt,"(2^64k * (s-t)) mod (2^{64k+1}-1)");

  // (2^{64k+1}+1) * (2^{64k} * (s-t) mod (2^{64k+1}-1))
  // = 2^{64k+1} * (smt[0~k]) + smt[0~k]
  for (int i = 1; i <= k; ++i)
    t[k+i] = 0;
  uint64_t *smt_shifted = temp + 8 * (k+1);
  smt_shifted[0] = smt[0] << 1;
  for (int i = 1; i <= k; ++i)
    smt_shifted[i] = (smt[i] << 1) | (smt[i-1] >> 63);
  bignum_add(k+1, t+k, k+1, t+k, k+1, smt_shifted);
  bignum_add(2*k+1, t, 2*k+1, t, k+1, smt);
  //print_bignum(2*k+1, t, "output");
}






static void copy_hilo_513bits(uint64_t *xh, uint64_t *xl, const uint64_t *x) {
  for (int i = 0; i < 8; ++i) {
    xl[i] = x[i];
    xh[i] = (x[8 + i] >> 1) | (x[8 + i + 1] << 63);
  }
  xl[8] = x[8] & 1;
  xh[8] = x[16] >> 1;
}

void bignum_add_9words(uint64_t *z, uint64_t *x, uint64_t *y);
void bignum_add_9words_1word(uint64_t *z, uint64_t *x, uint64_t y);
uint64_t bignum_sub_9words(uint64_t *z, uint64_t *x, uint64_t *y);
uint64_t bignum_ge_9words(uint64_t *x, uint64_t *y);
void bignum_optadd_9words(uint64_t *z, uint64_t *x, uint64_t cond, uint64_t *y);
uint64_t bignum_optadd_8words(uint64_t *z, uint64_t *x, uint64_t cond, uint64_t *y);
void bignum_optsub_9words(uint64_t *z, uint64_t *x, uint64_t cond, uint64_t *y);
void bignum_optneg_9words(uint64_t *z, uint64_t cond, uint64_t *x);

void bignum_add_mod_2_to_513_minus1(uint64_t *z, uint64_t *x, uint64_t *y);
uint64_t bignum_absdiff_9words(uint64_t *z, uint64_t *x, uint64_t *y);
void bignum_modoptneg_mod_2_to_513_plus1(uint64_t *z, uint64_t cond, uint64_t *x);
void bignum_ge_optsub_2_to_513_minus1(uint64_t *z);
void bignum_sub_optadd_2_to_513_minus1(uint64_t *z, uint64_t *x, uint64_t *y);
void bignum_sub_optadd_2_to_513_plus1(uint64_t *z, uint64_t *x, uint64_t *y);
void bignum_add_hi_lo_mod_2_to_513_minus1(uint64_t *z);

// Given t: 17 words, calculate t mod 2^513-1 and store at t.
void mod_2_to_513_minus1(uint64_t *t);

// Given t: 17 words, calculate t mod 2^513+1 and store at t.
// temp must be 18 words.
static void mod_2_to_513_plus1(uint64_t *t, uint64_t *temp) {
  uint64_t *t_hi = temp;
  uint64_t *t_lo = temp + 9;
  copy_hilo_513bits(t_hi, t_lo, t);

  bignum_sub_optadd_2_to_513_plus1(t, t_lo, t_hi);
}


static inline void mul_513(uint64_t *z, uint64_t *x, uint64_t *y) {
  bignum_mul_8_16_neon(z, x, y);

  int k = 8;
  uint64_t xmsb = x[k], ymsb = y[k];
  ASSERT(xmsb < 2);
  ASSERT(ymsb < 2);
  uint64_t c1 = bignum_optadd_8words(z+k, z+k, xmsb, y);
  uint64_t c2 = bignum_optadd_8words(z+k, z+k, ymsb, x);
  z[2 * k] = c1 + c2 + (xmsb & ymsb);
}

void bignum_mul_mod_2_to_1026_minus1(
    uint64_t *z, uint64_t *x, uint64_t *y, uint64_t *temp) {
  int k = 8;
  // x = 2^(64k+1) xh + xl
  // y = 2^(64k+1) yh + yl
  uint64_t *xl = temp;
  uint64_t *xh = temp + (k + 1);
  uint64_t *yl = temp + 2 * (k + 1);
  uint64_t *yh = temp + 3 * (k + 1);
  copy_hilo_513bits(xh, xl, x);
  copy_hilo_513bits(yh, yl, y);

  // xhml = |xh-xl|, xhml_sgn = xh < xl
  // yhml = |yh-yl|, yhml_sgn = yh < yl
  uint64_t *xhml = temp + 4 * (k + 1);
  uint64_t xhml_sgn = bignum_absdiff_9words(xhml, xh, xl);
  uint64_t *yhml = temp + 5 * (k + 1);
  uint64_t yhml_sgn = bignum_absdiff_9words(yhml, yh, yl);

  // 1. |xh-xl|*|yh-yl| mod (2^(64k+1)+1)
  //    First, do |xh-xl|*|yh-yl|
  uint64_t *t = z;
  mul_513(t, xhml, yhml);

  //    Second, do .. mod (2^(64k+1)+1).
  mod_2_to_513_plus1(t, temp + 8 * (k+1));
  bignum_modoptneg_mod_2_to_513_plus1(t, yhml_sgn^xhml_sgn, t);

  // 2. (xh+xl)(yh+yl) mod (2^(64k+1)-1)
  //    First, do xh+xl mod (2^(64k+1)-1) and yh+yl mod (2^(64k+1)-1)

  // xhpl = xh+xl
  // yhpl = yh+yl
  uint64_t *xhpl = temp + 6 * (k + 1);
  uint64_t *yhpl = temp + 7 * (k + 1);
  // NOTE: this can return 2^513-1 as well. This will be reduced by mod_2_to_513_minus1
  bignum_add_mod_2_to_513_minus1(xhpl, xh, xl);
  // NOTE: this can return 2^513-1 as well. This will be reduced by mod_2_to_513_minus1
  bignum_add_mod_2_to_513_minus1(yhpl, yh, yl);

  //    Second, do ((xh+xl) mod (2^(64k+1)-1)) * ((yh+yl) mod (2^(64k+1)-1))
  uint64_t *s = temp + 2 * (k + 1);
  mul_513(s, xhpl, yhpl);

  //    Finally, do .. mod (2^(64k+1)-1)
  mod_2_to_513_minus1(s);

  // Now, from s and t, reconstruct the answer.
  // t + (2^{64k+1}+1) * (2^{64k} * (s-t) mod (2^{64k+1}-1))
  // (s-t) mod (2^{64k+1}-1)
  uint64_t *smt = temp + 9 * (k+1);
  // let z = s - t in z >= 0 ? z : (z + 2^513-1)
  bignum_sub_optadd_2_to_513_minus1(smt, s, t);

  // (2^{64k} * (s-t) mod (2^{64k+1}-1))
  uint64_t smt_lsb = smt[0] & 1;
  for (int i = 0; i < k; ++i)
    smt[i] = (smt[i] >> 1) | (smt[i+1] << 63);
  smt[k] = (smt[k] >> 1) + smt_lsb;

  // (2^{64k+1}+1) * (2^{64k} * (s-t) mod (2^{64k+1}-1))
  // = 2^{64k+1} * (smt[0~k]) + smt[0~k]
  for (int i = 1; i <= k; ++i)
    t[k+i] = 0;
  uint64_t *smt_shifted = temp + 8 * (k+1);
  smt_shifted[0] = smt[0] << 1;
  for (int i = 1; i <= k; ++i)
    smt_shifted[i] = (smt[i] << 1) | (smt[i-1] >> 63);
  bignum_add_9words(t+k, t+k, smt_shifted);
  bignum_add(2*k+1, t, 2*k+1, t, k+1, smt);
}
