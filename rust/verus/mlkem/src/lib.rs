use vstd::prelude::*;

verus! {

const N      : usize = 256;
const Q      : i32 = 3329;
const HALF_Q : i32 = 1665;
const QINV   : u32 = 62209;

const U16_MAX_AS_I32 : i32 = u16::MAX as i32;
const U16_MAX_AS_U32 : u32 = u16::MAX as u32;
const I16_MIN_AS_I32 : i32 = i16::MIN as i32;
const I16_MAX_AS_I32 : i32 = i16::MAX as i32;

// MRB = Montgomery Reduction Bound
const MRB : i32 = 32768 * (HALF_Q - 1);

type Poly = [i16; N];

fn montgomery_reduce (a : i32) -> (r : i16)
  requires -MRB <= a <= MRB
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
  assert (-MRB <= (a as i32) * (b as i32) <= MRB) by (nonlinear_arith)
    requires -HALF_Q < b < HALF_Q;

  let arg : i32 = (a as i32) * (b as i32);

  return montgomery_reduce (arg);
}

#[verifier::loop_isolation(false)]
fn ntt_butterfly_block (r : &mut Poly, zeta : i16, start : usize, len : usize, bound : i16)
  requires start < N,
           1 <= len <= (N / 2),
           start + 2 * len <= N,
           0 <= bound < i16::MAX - Q as i16,
           -HALF_Q < zeta < HALF_Q,

           forall|i:int| 0 <= i < start ==> -(bound + Q) < old(r)[i],
           forall|i:int| 0 <= i < start ==> old(r)[i] < bound + Q,

           forall|i:int| start <= i < N ==> -bound < old(r)[i],
           forall|i:int| start <= i < N ==> old(r)[i] < bound,

  ensures  forall|i:int| 0 <= i < start + 2 * len ==> -(bound + Q) < r[i],
           forall|i:int| 0 <= i < start + 2 * len ==> r[i] < bound + Q,
           forall|i:int| start + 2 * len <= i < N ==> -bound < r[i],
           forall|i:int| start + 2 * len <= i < N ==> r[i] < bound,
{
  for j in iter: start .. start + len

// These invariant terms repeat the pre-condition regarding bound and zeta.
// These are only needed if verifier::loop_isolation(true) is enabled.
// If verifier::loop_isolation(false) (as above), then these terms are
// inferred from the pre-condition, iterator specification, and context.
//              1 <= len <= (N / 2),
//              start + 2 * len <= N,
//              0 <= bound < i16::MAX - Q as i16,
//              -HALF_Q < zeta < HALF_Q,
// These invariant terms can be inferred from the pre-condition and the
// bounds on the loop iterator
//              start <= j <= start + len,  // j       == start + len just before loop exit
//              j + len <= N,               // j + len == N           just before loop exit

              // Upper and lower bounds on r[i] are split here otherwise
              // Verus can't find the trigger automatically...
    invariant forall|i:int| 0 <= i < j ==> -(bound + Q) < r[i],
              forall|i:int| 0 <= i < j ==> r[i] < bound + Q,
              forall|i:int| j <= i < start + len ==> -bound < r[i],
              forall|i:int| j <= i < start + len ==> r[i] < bound,
              forall|i:int| start + len <= i < j + len ==> -(bound + Q) < r[i],
              forall|i:int| start + len <= i < j + len ==> r[i] < bound + Q,
              forall|i:int| j + len <= i < N ==> -bound < r[i],
              forall|i:int| j + len <= i < N ==> r[i] < bound,
  {
     let t : i16 = fqmul(r[j + len], zeta);
     r[j + len] = r[j] - t;
     r[j]       = r[j] + t;
  }
}



} // verus!
