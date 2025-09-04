#![allow(dead_code)]
#![allow(unused_imports)]

use vstd::prelude::*;

verus! {

  pub const N : usize = 256;
  type Poly = [i16; N];

  // Binding to C Reference implementation
  pub mod cref
  {
    use crate::Poly;

    #[repr(C)]
    #[repr(align(32))]
    #[derive(Debug, Copy, Clone)]
    pub struct mlk_poly {
        pub coeffs: Poly,
    }

    unsafe extern "C" {
      pub fn PQCP_MLKEM_NATIVE_MLKEM768_poly_ntt(r: *mut mlk_poly);
    }

    unsafe extern "C" {
      pub fn PQCP_MLKEM_NATIVE_MLKEM768_poly_reduce(r: *mut mlk_poly);
    }
  }

#[cfg(verus_keep_ghost)]
use vstd::{

    //arithmetic::mul::lemma_mul_inequality,
    //arithmetic::mul::lemma_mul_strict_inequality,
    bits::lemma_u32_low_bits_mask_is_mod,
    bits::lemma_low_bits_mask_values,

    bits::lemma_u64_shl_is_mul,
    arithmetic::power::lemma_pow_increases,
    arithmetic::power2::lemma2_to64,
    arithmetic::power2::pow2,
    arithmetic::power2::lemma_pow2,
    arithmetic::power2::lemma_pow2_adds,
};

// Public constants used in contracts
pub const Q         : i32 = 3329;
pub const HALF_Q    : i32 = 1665;
pub const NTT_BOUND : i32 = Q * 8;
// MRB = Montgomery Reduction Bound
pub const MRB : i32 = 32768 * (HALF_Q - 1);


// Private constants
const QINV16 : u16 = 3327;
const QINV32 : u32 = 62209;

// Montgomery factor R (2^16) and its inverse
pub const R: i32 = 65536;
pub const RINV : i32 = 169;

const U16_MAX_AS_I32 : i32 = u16::MAX as i32;
const U16_MAX_AS_U32 : u32 = u16::MAX as u32;
const I16_MIN_AS_I32 : i32 = i16::MIN as i32;
const I16_MAX_AS_I32 : i32 = i16::MAX as i32;

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


// Proof that RINV is the modular inverse of R modulo Q.
proof fn lemma_r_rinv_inverses_mod_q()
    ensures
        (R as int * RINV as int) % Q as int == 1,
{
    assert((R as int * RINV as int) % Q as int == 1) by (compute_only);
}

// Proof of the relation between the field modulus Q, Montgomery factor R, and
// their inverses.
proof fn lemma_q_r_montgomery_relation()
    ensures
        Q as int * QINV16 as int == R as int * RINV as int - 1,
{
    assert(Q as int * QINV16 as int == R as int * RINV as int - 1) by (compute_only);
}

proof fn lemma_montgomery_reduction_numerator(
    a: int,
    t: int,
    m: int,
    r: int,
    rinv: int,
    q: int,
    qinv: int,
)
    by (integer_ring)
    requires
        r != 0,
        t == a % r,
        m == (t * qinv) % r,
        q * qinv == r * rinv - 1,
    ensures
        (a + m * q) % r == 0,
{
}

proof fn lemma_cast_i32_to_u32_preserves_mod(s: i32)
    ensures
        (s as u32) as int % 4294967296 == s as int % 4294967296,
{
    assert(s >= 0 ==> s as u32 == s as int);
    assert(s < 0 ==> s as u32 == 4294967296int + (s as int)) by (bit_vector);
}

fn cast_unsigned_32(s: i32) -> (u: u32)
    ensures
        u as int % 4294967296 == s as int % 4294967296,
{
    proof { lemma_cast_i32_to_u32_preserves_mod(s) }
    s as u32
}

proof fn lemma_cast_u16_to_i16_preserves_mod(u: u16)
    ensures
        (u as i16) as int % 65536 == u as int % 65536,
{
    assert(u < 32768 ==> u as i16 == u as int);
    assert(u >= 32768 ==> u as i16 == -((65536 - u) as int)) by (bit_vector);
}

fn cast_signed_16(u: u16) -> (s: i16)
    ensures
        s as int % 65536 == u as int % 65536,
{
    proof { lemma_cast_u16_to_i16_preserves_mod(u) }
    u as i16
}


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

proof fn lemma_mask_is_mod(a: u32)
    ensures
        a & 0xffff == a % 0x10000,
{
    lemma_low_bits_mask_values();
    lemma_u32_low_bits_mask_is_mod(a, 16);
    lemma2_to64();
}

#[inline(never)]
pub fn montgomery_reduce_rod (a : i32) -> (r : i16)
  requires -MRB <= a <= MRB
  ensures -Q < r < Q
{
  let a_reduced  : u16 = a as u16;
  let a_inverted : u16 = ((a_reduced as u32) * QINV32) as u16;

  let t : i16 = a_inverted as i16;

  let r : i32 = a - ((t as i32) * Q);

  let result : i32 = r >> 16;

  assert (r == a - ((t as i32) * Q));
  assert (result == r >> 16);

  // Unfortunately `by (bit_vector)` requires inlining the
  // entire computation above here, including inserting constants
  // due to https://github.com/verus-lang/verus/issues/1858
  assert (-3329 < result < 3329) by (bit_vector)
    requires ({
      &&& result == r >> 16
      &&& r == (a - ((t as i32) * 3329))
      &&& t == a_inverted as i16
      &&& a_inverted == ((a_reduced as u32) * 62209u32) as u16
      &&& a_reduced == a as u16
      &&& -32768 * (1665 - 1) <= a <= 32768 * (1665 - 1)
  });
  return result as i16;
}

#[inline(never)]
#[verifier::nonlinear]
pub exec fn montgomery_reduce_mike(a: i32) -> (u: i16)
    requires -MRB <= a <= MRB
    ensures
        u as int % Q as int == (a as int * RINV as int) % Q as int,
        -Q < u < Q,
{
    // Reduce a modulo R.
    let au = cast_unsigned_32(a);
    let amod = au & 0xffff;
    assert(amod == au as int % R as int) by {
        lemma_mask_is_mod(au);
    };
    let t = amod as u16;
    assert(t == a % R);

    // Compute t * Q' mod R.
    let m = t.wrapping_mul(QINV16);

    // Cast to a signed representative.
    let ms = cast_signed_16(m);

    // Compute m*Q.
    let m_q = (ms as i32) * (Q as i32);

    // Compute a + m*Q, and prove it is a multiple of R.
    let n = a + m_q;

    // Prove: a + m*Q = 0 (mod R).
    assert(n as int % R as int == 0) by {
        lemma_montgomery_reduction_numerator(
            a as int,
            t as int,
            m as int,
            R as int,
            RINV as int,
            Q as int,
            QINV16 as int,
        );
    };

    // Compute (a + m * Q) / R.
    let u = n / R;

    return u as i16;
}


#[inline(never)]
pub fn fqmul (a : i16, b : i16) -> (r : i16)
  requires -HALF_Q < b < HALF_Q
  ensures -Q < r < Q
{
  // A bit of non-linear arithmetic is required by prove bounds on a*b
  assert (-MRB <= (a as i32) * (b as i32) <= MRB) by (nonlinear_arith)
    requires -HALF_Q < b < HALF_Q;

  let arg : i32 = (a as i32) * (b as i32);

  return montgomery_reduce_rod (arg);
}

#[inline(never)]
#[verifier::loop_isolation(false)]
pub fn ntt_butterfly_block (r : &mut Poly, zeta : i16, start : usize, len : usize, _bound : i16)
  requires start < N,
           1 <= len <= (N / 2),
           start + 2 * len <= N,
           0 <= _bound < i16::MAX - Q as i16,
           -HALF_Q < zeta < HALF_Q,

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

pub fn clen (layer : i16) -> (len : usize)
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

pub fn ck (layer : i16) -> (k : usize)
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



#[inline(never)]
#[verifier::loop_isolation(false)]
pub fn ntt_layer (r : &mut Poly, layer : i16)
  requires 1 <= layer <= 7,
           forall|i:int| 0 <= i < N ==> (-layer * (Q as i16)) < #[trigger] old(r)[i] < (layer * (Q as i16)),
  ensures  forall|i:int| 0 <= i < N ==> (-(layer + 1) * (Q as i16)) < #[trigger] r[i] < ((layer + 1) * (Q as i16)),
{
  broadcast use lemma_u64_shl_is_mul;

  let     len : usize = clen (layer);
  let mut k   : usize = ck (layer);

  assert(len * k == 128) by {
    lemma_pow2_adds((layer - 1) as nat, (8 - layer) as nat);
    lemma2_to64();
  }

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

const TWO26 : i32 = 67_108_864;
const TWO25 : i32 = 33_554_432;
const MAGIC : i32 = 20_159; // floor(2**26/Q)

#[inline(never)]
pub fn barrett_reduce(a : i16) -> (r : i16)
  ensures -HALF_Q < r < HALF_Q
{
  let t  : i32 = MAGIC * a as i32;
  assert(i16::MIN as i32 * MAGIC <= t <= i16::MAX as i32 * MAGIC) by (compute);

  let t2 : i32 = t + TWO25;
  assert((i16::MIN as i32 * MAGIC) + TWO25 <= t2 <= (i16::MAX as i32 * MAGIC) + TWO25);

  assert(-1i32 >> 1 == -1i32) by (bit_vector);

  let t3 : i32 = t2 >> 26;

  // bit_vector proofs unfortunately require restating the whole
  // proof context.
  assert({
    &&& (-10 <= t3 <= 10)
    &&& -1665 < ((a as i32 - t3 * 3329) as i16) < 1665
  }) by (bit_vector)
    requires
      ({
        &&& (i16::MIN as i32 * 20_159) + 33_554_432 <= t2 <= (i16::MAX as i32 * 20_159) + 33_554_432
        &&& t3 == t2 >> 26
        &&& t2 == t + 33_554_432
        &&& t == 20_159 * a
      });

  // if t3 bounded by +/-10 then t3 * Q needs to be evaluated in 32-bits
  let t4 : i32 = a as i32 - t3 * Q;
  let t5 : i16 = t4 as i16;

  return t5;
}

#[inline(never)]
pub fn signed_to_unsigned_q(a : i16) -> (r : i16)
  requires -Q < a < Q
  ensures 0 <= r < Q
{
  let adjustment : i32 = if a < 0 {Q} else {0};
  return (a as i32 + adjustment) as i16;
}


#[inline(never)]
pub fn poly_reduce (r : &mut Poly)
  requires forall|i:int| 0 <= i < N ==> -NTT_BOUND < #[trigger] old(r)[i] < NTT_BOUND,
  ensures forall|i:int| 0 <= i < N ==> 0 <= #[trigger] r[i] < Q,
{
  for i in 0 .. N
    invariant 0 <= i <= N,
              forall|k:int| 0 <= k < i ==> 0 <= #[trigger] r[k] < Q,
  {
    r[i] = signed_to_unsigned_q(barrett_reduce(r[i]));
  }
}

#[inline(never)]
#[verifier::loop_isolation(false)]
pub fn poly_ntt (r : &mut Poly)
  requires forall|i:int| 0 <= i < N ==> -Q < #[trigger] old(r)[i] < Q,
  ensures  forall|i:int| 0 <= i < N ==> -NTT_BOUND < #[trigger] r[i] < NTT_BOUND,
{
  for layer in 1i16 .. 8
    invariant 1 <= layer <= 8,
              forall|i:int| 0 <= i < N ==> (-layer * (Q as i16)) < #[trigger] r[i] < layer * (Q as i16),
  {
    ntt_layer(r, layer);
  }
}


} // verus!

#[cfg(test)]
mod tests {
    use super::*;

    fn pp(r: Poly) {
        for i in r.iter() {
            print!("{} ", i);
        }
        println!("END");
    }

    #[test]
    fn test_montgomery_reduce() {
        for a in -MRB..=MRB {
            let u_rod = montgomery_reduce_rod(a);
            let u_mike = montgomery_reduce_mike(a);

	    // Normalize results to 0 .. Q
            let urq = if u_rod >= 0 {u_rod} else {u_rod + Q as i16};
            let umq = if u_mike >= 0 {u_mike} else {u_mike + Q as i16};

            assert!((u_rod as i32) > -Q && (u_rod as i32) < Q);
            assert!((u_mike as i32) > -Q && (u_mike as i32) < Q);

            if urq != umq
	    {
               println!("input {} rod {}, mike {}", a, urq, umq);
	    }
            assert!(urq == umq);
        }
    }

    // Run with "cargo test -- --nocapture" to see the output of this one
    #[test]
    fn test_poly_ntt() {
        use cpucycles::CpuCycles;

        const INIT_P: Poly = [3i16; N];

        let cpu: CpuCycles = CpuCycles::new();
        println!("libcpucycles version: {}", cpu.version());
        println!("libcpucycles implem : {}", cpu.implementation());

        let mut p = cref::mlk_poly { coeffs: INIT_P };

        let start = cpu.get();
        for _i in 0..1000 {
            poly_ntt(&mut p.coeffs);
            poly_reduce(&mut p.coeffs);
        }
        let end = cpu.get();
        pp(p.coeffs);

        p = cref::mlk_poly { coeffs: INIT_P };
        let start2 = cpu.get();
        for _i in 0..1000 {
            unsafe {
                cref::PQCP_MLKEM_NATIVE_MLKEM768_poly_ntt(&mut p);
            }
            unsafe {
                cref::PQCP_MLKEM_NATIVE_MLKEM768_poly_reduce(&mut p);
            }
        }
        let end2 = cpu.get();
        pp(p.coeffs);

        println!("Rust Cycles = {}", end - start);
        println!("   C Cycles = {}", end2 - start2);
    }
}
