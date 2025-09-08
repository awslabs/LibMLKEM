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
void mlk_poly_reduce(mlk_poly *r)
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
void  mlk_poly_ntt(mlk_poly *r)
__contract__(
  requires(memory_no_alias(r, sizeof(mlk_poly)))
  requires(array_abs_bound(r->coeffs, 0, MLKEM_N, MLKEM_Q))
  assigns(memory_slice(r, sizeof(mlk_poly)))
  ensures(array_abs_bound(r->coeffs, 0, MLKEM_N, MLK_NTT_BOUND))
);

#endif /* !MLK_POLY_H */
