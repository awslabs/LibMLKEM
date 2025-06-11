// SPDX-License-Identifier: Apache-2.0

#include "mlkem.h"

// QINV == -3327 converted to uint16_t == -3327 + 65536 == 62209
static const uint32_t QINV = 62209;  // q^-1 mod 2^16


/*************************************************
 * Name:        cast_uint16_to_int16
 *
 * Description: Cast uint16 value to int16
 *
 * Returns:
 *   input x in     0 .. 32767: returns value unchanged
 *   input x in 32768 .. 65535: returns (x - 65536)
 **************************************************/
#ifdef CBMC
#pragma CPROVER check push
#pragma CPROVER check disable "conversion"
#endif
static inline int16_t cast_uint16_to_int16(uint16_t x) {
  // PORTABILITY: This relies on uint16_t -> int16_t
  // being implemented as the inverse of int16_t -> uint16_t,
  // which is implementation-defined (C99 6.3.1.3 (3))
  //
  // CBMC (correctly) fails to prove this conversion is OK,
  // so we have to suppress that check here
  return (int16_t)x;
}
#ifdef CBMC
#pragma CPROVER check pop
#endif

/*************************************************
 * Name:        montgomery_reduce
 *
 * Description: Montgomery reduction; given a 32-bit integer a, computes
 *              16-bit integer congruent to a * R^-1 mod q, where R=2^16
 *
 * Arguments:   - int32_t a: input integer to be reduced
 *
 * Returns:     integer congruent to a * R^-1 modulo q
 *
 *              Bounds: For any C such that |a| < q * C, the return value
 *              has absolute value < q (C/2^16 + 1/2).
 *
 *              Notable special cases:
 *              - The Montgomery multiplication of a value of absolute value
 *                < q * C with a signed-canonical value ( < q/2 ) has
 *                absolute value q * (0.0254 * C + 1/2).
 *              - The Montgomery multiplication of a value of absolute value
 *                < q * C with a value t of |t| < q has absolute value
 *                < q * (0.0508 * C + 1/2).
 *              - The Montgomery multiplication of a value of absolute value
 *                < C with a value of abs < q has absolute value
 *                < q (C/2^16 + 1/2).
 **************************************************/
int16_t montgomery_reduce(int32_t a) {
  // Bounds on paper
  //
  // - Case |a| < q * C, for some C
  //
  // |t| <= |a|/2^16 + |t|*q/2^16
  //      < q * C / 2^16 + q/2
  //      = q (C/2^16 + 1/2)
  //
  // - Case |a| < (q/2) * C * q, for some C
  //
  // Replace C -> C * q in the above and estimate
  // q / 2^17 < 0.0254.

  //  Compute a*q^{-1} mod 2^16 in unsigned representatives
  const uint16_t a_reduced = a & UINT16_MAX;
  const uint16_t a_inverted = (a_reduced * QINV) & UINT16_MAX;

  // Lift to signed canonical representative mod 2^16.
  const int16_t t = cast_uint16_to_int16(a_inverted);

  int32_t r = a - ((int32_t)t * MLKEM_Q);

  // PORTABILITY: Right-shift on a signed integer is, strictly-speaking,
  // implementation-defined for negative left argument. Here,
  // we assume it's sign-preserving "arithmetic" shift right. (C99 6.5.7 (5))
  r = r >> 16;

  return (int16_t)r;
}

int16_t fqmul(int16_t a, int16_t b) {
  int16_t res = montgomery_reduce((int32_t)a * (int32_t)b);
  return res;
}

void poly_tomont(poly *r) {
  int i;
  const int16_t f = (1ULL << 32) % MLKEM_Q;  // 1353
  for (i = 0; i < MLKEM_N; i++)
      // clang-format off
    ASSIGNS(i, OBJECT_WHOLE(r))
    INVARIANT(i >= 0 && i <= MLKEM_N)
    INVARIANT(ARRAY_IN_BOUNDS(int, k, 0, (i - 1), r->coeffs, -(MLKEM_Q - 1), (MLKEM_Q - 1)))
    DECREASES(MLKEM_N - i)
    // clang-format on
    {
      r->coeffs[i] = fqmul(r->coeffs[i], f);
    }
}
