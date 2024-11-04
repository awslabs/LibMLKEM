// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>
#include "cbmc.h"

#define MLKEM_K 3 /* Change this for different security strengths */
#define MLKEM_N 256
#define MLKEM_Q 3329
#define HALF_Q ((MLKEM_Q + 1) / 2)  // 1665

#define DEFAULT_ALIGN 32
#define ALIGN __attribute__((aligned(DEFAULT_ALIGN)))
#define ALWAYS_INLINE __attribute__((always_inline))

/*
 * Elements of R_q = Z_q[X]/(X^n + 1). Represents polynomial
 * coeffs[0] + X*coeffs[1] + X^2*coeffs[2] + ... + X^{n-1}*coeffs[n-1]
 */
typedef struct {
  int16_t coeffs[MLKEM_N];
} ALIGN poly;




/*************************************************
 * Name:        montgomery_reduce
 *
 * Description: Montgomery reduction
 *
 * Arguments:   - int32_t a: input integer to be reduced
 *                  Must be smaller than 2 * q * 2^15 in absolute value.
 *
 * Returns:     integer congruent to a * R^-1 modulo q,
 *              smaller than 3/2 q in absolute value.
 **************************************************/
int16_t montgomery_reduce(int32_t a)
    // clang-format off
REQUIRES(a > -(2 * MLKEM_Q * 32768))
REQUIRES(a <  (2 * MLKEM_Q * 32768))
ENSURES(RETURN_VALUE > -(3 * HALF_Q) && RETURN_VALUE < (3 * HALF_Q));
// clang-format on

/*************************************************
 * Name:        fqmul
 *
 * Description: Montgomery multiplication modulo q=3329
 *
 * Arguments:   - int16_t a: first factor
 *                  Can be any int16_t.
 *              - int16_t b: second factor.
 *                  Must be signed canonical (abs value <(q+1)/2)
 *
 * Returns 16-bit integer congruent to a*b*R^{-1} mod q, and
 * smaller than q in absolute value.
 *
 **************************************************/
int16_t fqmul(int16_t a, int16_t b)
    // clang-format off
REQUIRES(b > -HALF_Q)
REQUIRES(b < HALF_Q)
ENSURES(RETURN_VALUE > -MLKEM_Q && RETURN_VALUE < MLKEM_Q);
// clang-format on


/*************************************************
 * Name:        poly_tomont
 *
 * Description: Inplace conversion of all coefficients of a polynomial
 *              from normal domain to Montgomery domain
 *
 *              Bounds: Output < q in absolute value.
 *
 * Arguments:   - poly *r: pointer to input/output polynomial
 **************************************************/
void poly_tomont(poly *r)
    // clang-format off
REQUIRES(r != NULL && IS_FRESH(r, sizeof(poly)))
ASSIGNS(OBJECT_WHOLE(r))
ENSURES(ARRAY_IN_BOUNDS(int, k, 0, MLKEM_N - 1, r->coeffs, -(MLKEM_Q - 1), (MLKEM_Q - 1)));
// clang-format on
