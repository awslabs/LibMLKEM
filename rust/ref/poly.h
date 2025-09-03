/*
 * Copyright (c) The mlkem-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/* References
 * ==========
 *
 * - [FIPS203]
 *   FIPS 203 Module-Lattice-Based Key-Encapsulation Mechanism Standard
 *   National Institute of Standards and Technology
 *   https://csrc.nist.gov/pubs/fips/203/final
 */

#ifndef MLK_POLY_H
#define MLK_POLY_H

#include <stddef.h>
#include <stdint.h>
#include "cbmc.h"
#include "common.h"
#include "debug.h"
#include "verify.h"

/* Absolute exclusive upper bound for the output of the inverse NTT */
#define MLK_INVNTT_BOUND (8 * MLKEM_Q)

/* Absolute exclusive upper bound for the output of the forward NTT */
#define MLK_NTT_BOUND (8 * MLKEM_Q)

/*
 * Elements of R_q = Z_q[X]/(X^n + 1). Represents polynomial
 * coeffs[0] + X*coeffs[1] + X^2*coeffs[2] + ... + X^{n-1}*coeffs[n-1]
 */
typedef struct
{
  int16_t coeffs[MLKEM_N];
} MLK_ALIGN mlk_poly;

/*
 * INTERNAL presentation of precomputed data speeding up
 * the base multiplication of two polynomials in NTT domain.
 */
typedef struct
{
  int16_t coeffs[MLKEM_N >> 1];
} MLK_ALIGN mlk_poly_mulcache;

/*************************************************
 * Name:        mlk_cast_uint16_to_int16
 *
 * Description: Cast uint16 value to int16
 *
 * Returns:
 *   input x in     0 .. 32767: returns value unchanged
 *   input x in 32768 .. 65535: returns (x - 65536)
 **************************************************/
#define MLK_DEFAULT_INLINE __attribute__((noinline))

#ifdef CBMC
#pragma CPROVER check push
#pragma CPROVER check disable "conversion"
#endif
static MLK_ALWAYS_INLINE int16_t mlk_cast_uint16_to_int16(uint16_t x)
{
  /*
   * PORTABILITY: This relies on uint16_t -> int16_t
   * being implemented as the inverse of int16_t -> uint16_t,
   * which is implementation-defined (C99 6.3.1.3 (3))
   * CBMC (correctly) fails to prove this conversion is OK,
   * so we have to suppress that check here
   */
  return (int16_t)x;
}
#ifdef CBMC
#pragma CPROVER check pop
#endif

/*************************************************
 * Name:        mlk_montgomery_reduce
 *
 * Description: Generic Montgomery reduction; given a 32-bit integer a, computes
 *              16-bit integer congruent to a * R^-1 mod q, where R=2^16
 *
 * Arguments:   - int32_t a: input integer to be reduced, of absolute value
 *                smaller or equal to INT32_MAX - 2^15 * MLKEM_Q.
 *
 * Returns:     integer congruent to a * R^-1 modulo q, with absolute value
 *                <= ceil(|a| / 2^16) + (MLKEM_Q + 1)/2
 *
 **************************************************/
static MLK_DEFAULT_INLINE int16_t mlk_montgomery_reduce(int32_t a)
__contract__(
    requires(a < +(INT32_MAX - (((int32_t)1 << 15) * MLKEM_Q)) &&
	     a > -(INT32_MAX - (((int32_t)1 << 15) * MLKEM_Q)))
    /* We don't attempt to express an input-dependent output bound
     * as the post-condition here. There are two call-sites for this
     * function:
     * - The base multiplication: Here, we need no output bound.
     * - mlk_fqmul: Here, we inline this function and prove another spec
     *          for mlk_fqmul which does have a post-condition bound. */
)
{
  /* check-magic: 62209 == unsigned_mod(pow(MLKEM_Q, -1, 2^16), 2^16) */
  const uint32_t QINV = 62209;

  /*  Compute a*q^{-1} mod 2^16 in unsigned representatives */
  const uint16_t a_reduced = a & UINT16_MAX;
  const uint16_t a_inverted = (a_reduced * QINV) & UINT16_MAX;

  /* Lift to signed canonical representative mod 2^16. */
  const int16_t t = mlk_cast_uint16_to_int16(a_inverted);

  int32_t r;

  mlk_assert(a < +(INT32_MAX - (((int32_t)1 << 15) * MLKEM_Q)) &&
             a > -(INT32_MAX - (((int32_t)1 << 15) * MLKEM_Q)));

  r = a - ((int32_t)t * MLKEM_Q);

  /*
   * PORTABILITY: Right-shift on a signed integer is, strictly-speaking,
   * implementation-defined for negative left argument. Here,
   * we assume it's sign-preserving "arithmetic" shift right. (C99 6.5.7 (5))
   */
  r = r >> 16;
  /* Bounds: |r >> 16| <= ceil(|r| / 2^16)
   *                   <= ceil(|a| / 2^16 + MLKEM_Q / 2)
   *                   <= ceil(|a| / 2^16) + (MLKEM_Q + 1) / 2
   *
   * (Note that |a >> n| = ceil(|a| / 2^16) for negative a)
   */
  return (int16_t)r;
}

#define mlk_poly_reduce MLK_NAMESPACE(poly_reduce)
/*************************************************
 * Name:        mlk_poly_reduce
 *
 * Description: Converts polynomial to _unsigned canonical_ representatives.
 *
 *              The input coefficients can be arbitrary integers in int16_t.
 *              The output coefficients are in [0,1,...,MLKEM_Q-1].
 *
 * Arguments:   - mlk_poly *r: pointer to input/output polynomial
 *
 * Specification: Normalizes on unsigned canoncial representatives
 *                ahead of calling @[FIPS203, Compress_d, Eq (4.7)].
 *                This is not made explicit in FIPS 203.
 *
 **************************************************/
/*
 * NOTE: The semantics of mlk_poly_reduce() is different in
 * the reference implementation, which requires
 * signed canonical output data. Unsigned canonical
 * outputs are better suited to the only remaining
 * use of mlk_poly_reduce() in the context of (de)serialization.
 */
MLK_INTERNAL_API
void MLK_DEFAULT_INLINE mlk_poly_reduce(mlk_poly *r)
__contract__(
  requires(memory_no_alias(r, sizeof(mlk_poly)))
  assigns(memory_slice(r, sizeof(mlk_poly)))
  ensures(array_bound(r->coeffs, 0, MLKEM_N, 0, MLKEM_Q))
);

#define mlk_poly_ntt MLK_NAMESPACE(poly_ntt)
/*************************************************
 * Name:        mlk_poly_ntt
 *
 * Description: Computes negacyclic number-theoretic transform (NTT) of
 *              a polynomial in place.
 *
 *              The input is assumed to be in normal order and
 *              coefficient-wise bound by MLKEM_Q in absolute value.
 *
 *              The output polynomial is in bitreversed order, and
 *              coefficient-wise bound by MLK_NTT_BOUND in absolute value.
 *
 *              (NOTE: Sometimes the input to the NTT is actually smaller,
 *               which gives better bounds.)
 *
 * Arguments:   - mlk_poly *p: pointer to in/output polynomial
 *
 * Specification: Implements @[FIPS203, Algorithm 9, NTT]
 *
 **************************************************/
MLK_INTERNAL_API
void MLK_DEFAULT_INLINE mlk_poly_ntt(mlk_poly *r)
__contract__(
  requires(memory_no_alias(r, sizeof(mlk_poly)))
  requires(array_abs_bound(r->coeffs, 0, MLKEM_N, MLKEM_Q))
  assigns(memory_slice(r, sizeof(mlk_poly)))
  ensures(array_abs_bound(r->coeffs, 0, MLKEM_N, MLK_NTT_BOUND))
);

#endif /* !MLK_POLY_H */
