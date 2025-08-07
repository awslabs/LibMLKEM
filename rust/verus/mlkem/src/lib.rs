use vstd::prelude::*;

verus! {

#[cfg(verus_keep_ghost)]
use vstd::{

    //arithmetic::mul::lemma_mul_inequality,
    //arithmetic::mul::lemma_mul_strict_inequality,
    //bits::lemma_u32_low_bits_mask_is_mod,
    //bits::lemma_low_bits_mask_values,

    bits::lemma_u64_shl_is_mul,
    arithmetic::power::lemma_pow_increases,
    arithmetic::power2::lemma2_to64,
    arithmetic::power2::pow2,
    arithmetic::power2::lemma_pow2,
    arithmetic::power2::lemma_pow2_adds,
};

const N         : usize = 256;
const Q         : i32 = 3329;
const HALF_Q    : i32 = 1665;
const QINV      : u32 = 62209;
const NTT_BOUND : i32 = Q * 8;
const RINV      : i32 = 169;

const U16_MAX_AS_I32 : i32 = u16::MAX as i32;
const U16_MAX_AS_U32 : u32 = u16::MAX as u32;
const I16_MIN_AS_I32 : i32 = i16::MIN as i32;
const I16_MAX_AS_I32 : i32 = i16::MAX as i32;

// MRB = Montgomery Reduction Bound
const MRB : i32 = 32768 * (HALF_Q - 1);

type Poly = [i16; N];
type ZetaTable = [i16; 128];

const ZETAS : ZetaTable =
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
#[verifier::external_body]
fn u16toi16 (x : u16) -> (r : i16)
  ensures (x <= 32767) ==> (r == x),
          (x > 32768)  ==> (r == ((x as i32) - 65536i32) as i16)
{
  return x as i16;
}

// Ditto for i32 to u16 conversion
#[verifier::external_body]
fn i32tou16 (x : i32) -> (r : u16)
  ensures r == x & 0xFFFF,
          0 <= r <= u16::MAX,
{
  return x as u16;
}

// Ditto for u32 to u16 conversion
#[verifier::external_body]
fn u32tou16 (x : u32) -> (r : u16)
  ensures r == x & 0xFFFF,
          0 <= r <= u16::MAX,
{
  return x as u16;
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
fn ntt_butterfly_block (r : &mut Poly, zeta : i16, start : usize, len : usize, _bound : i16)
  requires start < N,
           1 <= len <= (N / 2),
           start + 2 * len <= N,
           0 <= _bound < i16::MAX - Q as i16,
           -HALF_Q < zeta < HALF_Q,

           // Q3: why old(r) here in the requires clause?
           forall|i:int| 0 <= i < start ==> -(_bound + Q) < #[trigger] old(r)[i] < _bound + Q,
           forall|i:int| start <= i < N ==> -_bound < #[trigger] old(r)[i] < _bound,

  ensures  forall|i:int| 0 <= i < start + 2 * len ==> -(_bound + Q) < #[trigger] r[i] < _bound + Q,
           forall|i:int| start + 2 * len <= i < N ==> -_bound < #[trigger] r[i] < _bound,
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

    invariant forall|i:int| 0 <= i < j ==> -(_bound + Q) < #[trigger] r[i] < _bound + Q,
              forall|i:int| j <= i < start + len ==> -_bound < #[trigger] r[i] < _bound,
              forall|i:int| start + len <= i < j + len ==> -(_bound + Q) < #[trigger] r[i] < _bound + Q,
              forall|i:int| j + len <= i < N ==> -_bound < #[trigger] r[i] < _bound,
  {
     let t : i16 = fqmul(r[j + len], zeta);
     r[j + len] = r[j] - t;
     r[j]       = r[j] + t;
  }
}


// TODO: move to vstd::arithmetic::power2
proof fn lemma_pow2_increases(e1: nat, e2: nat)
    requires
        e1 <= e2,
    ensures
        pow2(e1) <= pow2(e2),
{
    lemma_pow2(e1);
    lemma_pow2(e2);
    lemma_pow_increases(2, e1, e2);
}

// TODO: move to vstd::bits
proof fn lemma_u64_one_shl_is_pow2(shift: u64)
    requires
        0 <= shift < u64::BITS,
        pow2(shift as nat) <= u64::MAX,
    ensures
        1u64 << shift == pow2(shift as nat) as u64,
{
  let x = 1u64;
  assert((x << shift) == x * pow2(shift as nat)) by {
    lemma_u64_shl_is_mul(x, shift);
  };
}

fn clen (layer : i16) -> (len : usize)
  requires 1 <= layer <= 7,
  ensures 2 <= len <= 128,
          len as nat == pow2((8 - layer) as nat),
{
  let ul : u64 = 8 - layer as u64;
  assert (1 <= ul <= 7);
  let r : u64 = 1 << ul;

  assert(2 <= pow2(ul as nat) <= 128) by {
    lemma_pow2_increases(1, ul as nat);
    lemma_pow2_increases(ul as nat, 7);
    lemma2_to64();
  };

  assert (r == pow2(ul as nat)) by {
    lemma_u64_one_shl_is_pow2(ul as u64);
  };

  r as usize
}

fn ck (layer : i16) -> (k : usize)
  requires 1 <= layer <= 7,
  ensures 1 <= k <= 64,
          k as nat == pow2((layer - 1) as nat),
{
  let ul : u64 = (layer - 1) as u64;
  assert (0 <= ul <= 6);
  let r : u64 = 1 << ul;

  assert(1 <= pow2(ul as nat) <= 64) by {
    lemma_pow2_increases(0, ul as nat);
    lemma_pow2_increases(ul as nat, 6);
    lemma2_to64();
  };

  assert (r == pow2(ul as nat)) by {
    lemma_u64_one_shl_is_pow2(ul as u64);
  };

  r as usize
}



#[verifier::loop_isolation(false)]
fn ntt_layer (r : &mut Poly, layer : i16)
  requires 1 <= layer <= 7,
           forall|i:int| 0 <= i < N ==> (-layer * (Q as i16)) < #[trigger] old(r)[i] < (layer * (Q as i16)),
  ensures  forall|i:int| 0 <= i < N ==> (-(layer + 1) * (Q as i16)) < #[trigger] r[i] < ((layer + 1) * (Q as i16)),
{
  broadcast use lemma_u64_shl_is_mul;
  broadcast use lemma_pow2_adds;

  let     len : usize = clen (layer);
  let mut k   : usize = ck (layer);

  assert(2 <= len <= 128);
  assert(1 <= k <= 64);

  // It helps to know that len * k == 128.
  // Using the pow2 and bits lemmas, this all seems a bit long-winded.
  // Is there an easier and more elegant way?
  assert(len as nat == pow2((8 - layer) as nat));
  assert(k   as nat == pow2((layer - 1) as nat));
  assert((len as nat) * (k as nat) == pow2((8 - layer) as nat) * pow2((layer - 1) as nat));
  assert(pow2((8 - layer) as nat) * pow2((layer - 1) as nat) == pow2((8 - layer) as nat + (layer - 1) as nat));
  assert((8 - layer) as nat + (layer - 1) as nat == 7);
  assert(pow2((8 - layer) as nat) * pow2((layer - 1) as nat) == pow2(7));
  assert((len as nat) * (k as nat) == pow2(7));
  assert(pow2(7) == 128) by { lemma2_to64() };
  assert((len as nat) * (k as nat) == 128);
  // At last!
  assert(len * k == 128);

  let mut start : usize = 0;

  // Q5: Why does "256" here work ok, but "N" not OK?
  assert(2 * len * k == start + 256) by (nonlinear_arith)
    requires len * k == 128,
             start == 0;

  while start + 2 * len <= N
    invariant 1 <= layer <= 7,
              start < N + 2 * len,
              k <= N / 2,
              2 * len * k == start + N,
              forall|i:int| 0 <= i < start ==> (-(layer + 1) * (Q as i16)) < #[trigger] r[i] < ((layer + 1) * (Q as i16)),
              forall|i:int| start <= i < N ==> (-layer * (Q as i16)) < #[trigger] r[i] < (layer * (Q as i16)),
    decreases N - start,
  {
    let zeta : i16 = ZETAS[k];
    ntt_butterfly_block(r, zeta, start, len, layer * (Q as i16));

    // Adding 1 to k, and 2*len to start maintains the loop invariant,
    // but we need nonlinear_arith to establish that result, so...
    assert(2 * len * (k + 1) == (start + 2 * len) + N) by (nonlinear_arith)
      requires 2 * len * k == start + N;

    k += 1;
    start += 2 * len;
  }

}

const TWO25 : i32 = 33_554_432;
const MAGIC : i32 = 20_159; // floor(2**26/Q)

fn barrett_reduce(a : i16) -> (r : i16)
  ensures -HALF_Q < r < HALF_Q
{
  let t  : i32 = MAGIC * a as i32;
  assert(i16::MIN as i32 * MAGIC <= t <= i16::MAX as i32 * MAGIC) by (compute);

  let t2 : i32 = t + TWO25;
  assert((i16::MIN as i32 * MAGIC) + TWO25 <= t2 <= (i16::MAX as i32 * MAGIC) + TWO25);

  // Verus seems to get lost here...
  let t3 : i32 = t2 >> 26;

  assert(-10 <= t3) by (bit_vector)
    requires (i16::MIN as i32 * 20_159) + 33_554_432 <= t2 <= (i16::MAX as i32 * 20_159) + 33_554_432;

  assert(t3 <= 10) by (bit_vector)
    requires (i16::MIN as i32 * 20_159) + 33_554_432 <= t2 <= (i16::MAX as i32 * 20_159) + 33_554_432;

  // if t3 bounded by +/-10 then t3 * Q needs to be evaluated in 32-bits
  let t4 : i32 = a as i32 - t3 * Q;
  let t5 : i16 = t4 as i16;
  return t5;
}


#[verifier::loop_isolation(false)]
fn poly_ntt (r : &mut Poly)
  requires forall|i:int| 0 <= i < N ==> -Q < #[trigger] old(r)[i] < Q,
  ensures  forall|i:int| 0 <= i < N ==> -NTT_BOUND < #[trigger] old(r)[i] < NTT_BOUND,
{
  for layer in 1i16 .. 8
    invariant forall|i:int| 0 <= i < N ==> (-layer * (Q as i16)) < #[trigger] r[i] < layer * (Q as i16),
  {
    ntt_layer(r, layer);
  }
}


} // verus!

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_montgomery_reduce() {
        for a in -MRB ..= MRB {
            let u = montgomery_reduce(a);
            assert!((u as i32) > -Q && (u as i32) < Q);

            // Something isn't right here!
            assert_eq!(u % Q as i16, ((a as i64 * RINV as i64) % Q as i64) as i16);

        }
    }
}
