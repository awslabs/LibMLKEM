// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Check that Kani correctly verifies the contracts of
//! `montgomery_reduce` and `fqmul`.
//
// kani-flags: -Zfunction-contracts
const MLKEM_Q: i32 = 3329;
const HALF_Q: i32 = (MLKEM_Q + 1) / 2;  // 1665
const UINT16_MAX: i32 = 65535;
const QINV: u32 = 62209;

fn cast_uint16_to_int16(x:u16) -> i16 {
    return x as i16;
}

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
#[kani::requires(a > -(2 * MLKEM_Q * 32768) && a <  (2 * MLKEM_Q * 32768))]
#[kani::ensures(|y| *y as i32 > -(3 * HALF_Q) && (*y as i32) < (3 * HALF_Q))]
fn montgomery_reduce(a: i32) -> i16 {
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
  let a_reduced: u16 = (a & UINT16_MAX) as u16;
  let a_inverted: u16 = (a_reduced as u32 * QINV) as u16 & UINT16_MAX as u16;

  // Lift to signed canonical representative mod 2^16.
  let t: i16 = cast_uint16_to_int16(a_inverted);

  let mut r:i32 = a - (t as i32 * MLKEM_Q);

  // PORTABILITY: Right-shift on a signed integer is, strictly-speaking,
  // implementation-defined for negative left argument. Here,
  // we assume it's sign-preserving "arithmetic" shift right. (C99 6.5.7 (5))
  r = r >> 16;

  return r as i16;
}

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
#[kani::requires(b > -HALF_Q as i16 && b < HALF_Q as i16)]
#[kani::ensures(|y| *y > -MLKEM_Q as i16 && *y < MLKEM_Q as i16)]
fn fqmul(a: i16, b: i16) -> i16 {
  let res: i16 = montgomery_reduce(a as i32 * b as i32);
  return res;
}


#[kani::proof_for_contract(fqmul)]
fn check_fqmul() {
    let a = kani::any();
    let b = kani::any();
    fqmul(a, b);
}

#[kani::proof_for_contract(montgomery_reduce)]
fn check_montgomery_reduce() {
    let x = kani::any();
    montgomery_reduce(x);
}
