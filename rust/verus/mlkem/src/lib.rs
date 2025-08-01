use vstd::prelude::*;
use vstd::bits::*;
use vstd::arithmetic::power2::*;

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
type ZetaTable = [i16; 128];

const Zetas : ZetaTable =
  [
    -1044, -758,  -359,  -1517, 1493,  1422,  287,   202,  -171,  622,   1577,
    182,   962,   -1202, -1474, 1468,  573,   -1325, 264,  383,   -829,  1458,
    -1602, -130,  -681,  1017,  732,   608,   -1542, 411,  -205,  -1571, 1223,
    652,   -552,  1015,  -1293, 1491,  -282,  -1544, 516,  -8,    -320,  -666,
    -1618, -1162, 126,   1469,  -853,  -90,   -271,  830,  107,   -1421, -247,
    -951,  -398,  961,   -1508, -725,  448,   -1065, 677,  -1275, -1103, 430,
    555,   843,   -1251, 871,   1550,  105,   422,   587,  177,   -235,  -291,
    -460,  1574,  1653,  -246,  778,   1159,  -147,  -777, 1483,  -602,  1119,
    -1590, 644,   -872,  349,   418,   329,   -156,  -75,  817,   1097,  603,
    610,   1322,  -1285, -1465, 384,   -1215, -136,  1218, -1335, -874,  220,
    -1187, -1659, -1185, -1530, -1278, 794,   -1510, -854, -870,  478,   -108,
    -308,  996,   991,   958,   -1460, 1522,  1628,
  ];


// Verus can't directly model the semantics of u16 -> i16 conversion
// at the moment, so we wrap these conversions in a function with
// suitable postcondition for now..
fn u16toi16 (x : u16) -> (r : i16)
  ensures (x <= 32767) ==> (r == x),
          (x > 32768)  ==> (r == ((x as i32) - 65536i32) as i16)
{
  return #[verifier::truncate] (x as i16);
}

// Ditto for i32 to u16 conversion
fn i32tou16 (x : i32) -> (r : u16)
  ensures r == x & 0xFFFF,
          0 <= r <= u16::MAX,
{
  return #[verifier::truncate] (x as u16);
}

// Ditto for u32 to u16 conversion
fn u32tou16 (x : u32) -> (r : u16)
  ensures r == x & 0xFFFF,
          0 <= r <= u16::MAX,
{
  return #[verifier::truncate] (x as u16);
}

fn montgomery_reduce (a : i32) -> (r : i16)
  requires -MRB <= a <= MRB
  ensures -Q < r < Q
{
  let a_reduced  : u16 = i32tou16 (a);
  let a_inverted : u16 = u32tou16 ((a_reduced as u32) * QINV);

  let t : i16 = u16toi16 (a_inverted);

  let r : i32 = a - ((t as i32) * Q);

  let result : i32 = r >> 16;

  assert (r == a - ((t as i32) * Q));
  assert (result == r >> 16);

  // Q2: Help! How can I get these to prove?
  assert (result < Q);  // Can't prove this yet
  assert (result > -Q); // Can't prove this yet
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

           // Q3: why old(r) here in the requires clause?
           forall|i:int| 0 <= i < start ==> -(bound + Q) < #[trigger] old(r)[i] < bound + Q,
           forall|i:int| start <= i < N ==> -bound < #[trigger] old(r)[i] < bound,

  ensures  forall|i:int| 0 <= i < start + 2 * len ==> -(bound + Q) < #[trigger] r[i] < bound + Q,
           forall|i:int| start + 2 * len <= i < N ==> -bound < #[trigger] r[i] < bound,
{
  for j in iter: start .. start + len

// These invariant terms repeat the pre-condition regarding start, len, bound and zeta.
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

    invariant forall|i:int| 0 <= i < j ==> -(bound + Q) < #[trigger] r[i] < bound + Q,
              forall|i:int| j <= i < start + len ==> -bound < #[trigger] r[i] < bound,
              forall|i:int| start + len <= i < j + len ==> -(bound + Q) < #[trigger] r[i] < bound + Q,
              forall|i:int| j + len <= i < N ==> -bound < #[trigger] r[i] < bound,
  {
     let t : i16 = fqmul(r[j + len], zeta);
     r[j + len] = r[j] - t;
     r[j]       = r[j] + t;
  }
}


#[verifier::loop_isolation(false)]
fn ntt_layer (r : &mut Poly, layer : i16)
  requires 1 <= layer <= 7,
           forall|i:int| 0 <= i < N ==> (-layer * (Q as i16)) < #[trigger] old(r)[i] < (layer * (Q as i16)),
  ensures  forall|i:int| 0 <= i < N ==> (-(layer + 1) * (Q as i16)) < #[trigger] r[i] < ((layer + 1) * (Q as i16)),
{
  broadcast use lemma_u16_shr_is_div;

  // Q4: Compute len and prove 2 <= len <= 128.
  // This all seems a bit long-winded. Is there an easier way?
  let ul : u16 = layer as u16;
  assert(1 <= ul <= 7);
  assert(2 <= (256 >> ul) <= 128) by (bit_vector)
    requires 1 <= ul <= 7;

  let len : usize = N >> ul;

  assert(len == 256 as nat / pow2(ul as nat)); // Trigger lemma

  assert(2 <= len <= 128);

  // Compute k and prove 1 <= k <= 64.
  let ul1 : usize = (7 - layer) as usize;
  assert(0 <= ul1 <= 6);
  assert(1 <= (64 >> ul1) <= 64) by (bit_vector)
    requires 0 <= ul1 <= 6;

  let mut k : usize = 64 >> ul1;
  assert(1 <= k <= 64); // Proof fails here!



  let mut start : usize = 0;
//  assert(len * k == 128) by (nonlinear_arith);

//  assert(start + 2 * len <= N);

  // Q5: Why does "256" here work ok, but "N" not OK?
  assert(2 * len * k == start + 256) by (bit_vector)
    requires 1 <= layer <= 7,
             len == 256 >> (layer as u16),
             k == 64 >> (7 - layer) as usize,
             start == 0;

  while (start < N && k < N / 2)
    invariant 1 <= layer <= 7,
              start < N + 2 * len,
              k <= N / 2,
              2 * len * k == start + N,
              forall|i:int| 0 <= i < start ==> (-(layer + 1) * (Q as i16)) < #[trigger] r[i] < ((layer + 1) * (Q as i16)),
              forall|i:int| start <= i < N ==> (-layer * (Q as i16)) < #[trigger] r[i] < (layer * (Q as i16)),
    decreases N - start,
  {
    let zeta : i16 = Zetas[k];
    ntt_butterfly_block(r, zeta, start, len, layer * (Q as i16));
    k += 1;
    start += 2 * len;
  }

}

fn clen (layer : i16) -> (len : usize)
  requires 1 <= layer <= 7,
  ensures 2 <= len <= 128,
          len as nat == pow2((8 - layer) as nat),
{
  broadcast use lemma_u16_shl_is_mul;

  let ul : usize = (8 - layer as usize);
  assert (1 <= ul <= 7);
  let r : usize = 1 << ul;
  assert (r as nat == 1 * pow2(ul as nat)); // using lemma_u16_shl_is_mul;

  return r;

}

} // verus!
