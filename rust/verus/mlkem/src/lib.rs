use vstd::prelude::*;

verus! {

const Q      : i32 = 3329;
const HALF_Q : i32 = 1665;
const QINV   : u32 = 62209;

const MRB : i32 = i32::MAX - (32768 * Q);

const U16_MAX_AS_I32 : i32 = u16::MAX as i32;
const U16_MAX_AS_U32 : u32 = u16::MAX as u32;
const I16_MIN_AS_I32 : i32 = i16::MIN as i32;
const I16_MAX_AS_I32 : i32 = i16::MAX as i32;

fn montgomery_reduce (a : i32) -> (r : i16)
  requires -MRB < a < MRB
  ensures -Q < r < Q
{
  let a_reduced  : u16 = (a & U16_MAX_AS_I32) as u16;
  let a_inverted : u16 = (((a_reduced as u32) * QINV) & U16_MAX_AS_U32) as u16;

  let t : i16 = a_inverted as i16;

  let r : i32 = a - ((t as i32) * Q);

  let result : i32 = r >> 16;

  assert (r < Q);  // Can't prove this yet
  assert (r > -Q); // Can't prove this yet
  return result as i16;
}

fn fqmul (a : i16, b : i16) -> (r : i16)
  requires -HALF_Q < b < HALF_Q
  ensures -Q < r < Q
{
  // A bit of non-linear arithmetic is required by prove bounds on a*b
  assert (I16_MIN_AS_I32 * HALF_Q < (a as i32) * (b as i32) < -I16_MIN_AS_I32 * HALF_Q) by (nonlinear_arith)
    requires -HALF_Q < b < HALF_Q;

  let arg : i32 = (a as i32) * (b as i32);
  return montgomery_reduce (arg);
}


} // verus!
