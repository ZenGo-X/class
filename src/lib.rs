#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(dead_code)]
#![allow(clippy::many_single_char_names)]

include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

extern crate libc;
#[macro_use]
extern crate serde_derive;
extern crate curv;
extern crate hmac;
extern crate serde;
extern crate serde_json;
extern crate sha2;

use std::ffi::CStr;
use std::mem::swap;
use std::ops::Neg;
use std::{ptr, str};

use libc::c_char;

use curv::arithmetic::traits::*;
use curv::BigInt;

mod chinese_reminder_theorem;
pub mod primitives;

#[derive(PartialEq, Eq, Clone, Debug, Serialize, Deserialize)]
pub struct BinaryQF {
    pub a: BigInt,
    pub b: BigInt,
    pub c: BigInt,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct ABDeltaTriple {
    pub a: BigInt,
    pub b: BigInt,
    pub delta: BigInt,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct BinaryQFCompressed {
    pub a1: BigInt,
    pub t1: BigInt,
    pub g: BigInt,
    pub b0: BigInt,
    pub e: bool,
    pub delta: BigInt,
}

impl BinaryQF {
    pub fn binary_quadratic_form_disc(abdelta_triple: &ABDeltaTriple) -> Self {
        let a = abdelta_triple.a.clone();
        let b = abdelta_triple.b.clone();
        let delta = abdelta_triple.delta.clone();

        assert_eq!(delta.mod_floor(&BigInt::from(4)), BigInt::one());
        assert!(delta < BigInt::zero()); // in general delta can be positive but we don't deal with that case
        let c = (&b.pow(2) - &delta) / (BigInt::from(4) * &a);
        BinaryQF { a, b, c }
    }

    pub fn binary_quadratic_form_principal(delta: &BigInt) -> Self {
        let one = BigInt::one();
        assert_eq!(delta.mod_floor(&BigInt::from(4)), BigInt::one());
        assert!(delta < &BigInt::zero()); // in general delta can be positive but we don't deal with that case
        let a_b_delta = ABDeltaTriple {
            a: one.clone(),
            b: one,
            delta: delta.clone(),
        };
        BinaryQF::binary_quadratic_form_disc(&a_b_delta)
    }

    pub fn discriminant(&self) -> BigInt {
        // for negative delta we compute 4ac - b^2
        let abs_delta = BigInt::from(4) * &self.a * &self.c - &self.b * &self.b;
        assert!(abs_delta > BigInt::zero());
        -abs_delta
    }

    pub fn discriminant_sqrt(&self) -> BigInt {
        let disc = self.discriminant();
        disc.sqrt()
    }

    pub fn is_reduced(&self) -> bool {
        self.is_normal() && self.a <= self.c && !(self.a == self.c && self.b < BigInt::zero())
    }

    pub fn normalize(&self) -> Self {
        // assume delta<0 and a>0
        let a_sub_b: BigInt = &self.a - &self.b;
        let s_f = a_sub_b.div_floor(&(BigInt::from(2) * &self.a));

        BinaryQF {
            a: self.a.clone(),
            b: &self.b + BigInt::from(2) * &s_f * &self.a,
            c: &self.a * &s_f.pow(2) + &self.b * &s_f + &self.c,
        }
    }

    pub fn is_normal(&self) -> bool {
        self.b <= self.a && self.b > -(&self.a)
    }
    pub fn primeform(quad_disc: &BigInt, q: &BigInt) -> Self {
        let quad_disc_gen = bn_to_gen(quad_disc);

        let q_gen = bn_to_gen(q);

        let pf = unsafe { primeform(quad_disc_gen, q_gen, 3i64) };

        let bqf = BinaryQF::pari_qf_to_qf(pf);

        bqf.normalize()
    }

    pub fn compose(&self, qf2: &BinaryQF) -> Self {
        assert_eq!(self.discriminant(), qf2.discriminant());
        let qf_pari_a = self.qf_to_pari_qf();

        let qf_pari_b = qf2.qf_to_pari_qf();

        let qf_pari_c = unsafe { qfbcompraw(qf_pari_a, qf_pari_b) };

        BinaryQF::pari_qf_to_qf(qf_pari_c)
    }

    pub fn inverse(&self) -> Self {
        BinaryQF {
            a: self.a.clone(),
            b: self.b.clone().neg(),
            c: self.c.clone(),
        }
    }

    pub fn rho(&self) -> Self {
        let qf_new = BinaryQF {
            a: self.c.clone(),
            b: self.b.clone().neg(),
            c: self.a.clone(),
        };

        qf_new.normalize()
    }

    pub fn reduce(&self) -> Self {
        let mut h: BinaryQF;
        let mut h_new = self.clone();
        if !self.is_normal() {
            h_new = self.normalize();
        }
        h = h_new;
        while !h.is_reduced() {
            let h_new = h.rho();
            h = h_new;
        }
        h
    }

    pub fn exp(&self, n: &BigInt) -> BinaryQF {
        let pari_qf = self.qf_to_pari_qf();
        let pari_n = bn_to_gen(n);

        let pari_qf_exp = unsafe { nupow(pari_qf, pari_n, ptr::null_mut()) };

        BinaryQF::pari_qf_to_qf(pari_qf_exp)
    }
    // gotoNonMax: outputs: f=phi_q^(-1)(F), a binary quadratic form of disc. delta*conductor^2
    //      f is non normalized
    pub fn phi_q_to_the_minus_1(&self, conductor: &BigInt) -> BinaryQF {
        let two_a = &self.a * BigInt::from(2);
        let b_conductor: BigInt = &self.b * conductor;
        let b_new = b_conductor.mod_floor(&two_a);
        let disc = self.discriminant();
        let cond_square = conductor.pow(2);
        let delta = disc * cond_square;
        let abdelta = ABDeltaTriple {
            a: self.a.clone(),
            b: b_new,
            delta,
        };

        BinaryQF::binary_quadratic_form_disc(&abdelta)
    }

    // compute (p^(2),p,-)^k in class group of disc. delta
    pub fn expo_f(p: &BigInt, delta: &BigInt, k: &BigInt) -> BinaryQF {
        if k == &BigInt::zero() {
            return BinaryQF::binary_quadratic_form_principal(delta);
        }
        let mut k_inv = BigInt::mod_inv(k, p).unwrap();
        if k_inv.mod_floor(&BigInt::from(2)) == BigInt::zero() {
            k_inv -= p;
        };
        let k_inv_p = k_inv * p;
        let abdelta = ABDeltaTriple {
            a: p * p,
            b: k_inv_p,
            delta: delta.clone(),
        };

        BinaryQF::binary_quadratic_form_disc(&abdelta)
    }

    pub fn discrete_log_f(p: &BigInt, delta: &BigInt, c: &BinaryQF) -> BigInt {
        let principal_qf = BinaryQF::binary_quadratic_form_principal(delta);
        if c == &principal_qf {
            BigInt::zero()
        } else {
            let Lk = c.b.div_floor(p);

            BigInt::mod_inv(&Lk, p).unwrap()
        }
    }

    //we construct a pari qf from qf
    pub fn qf_to_pari_qf(&self) -> GEN {
        let a = bn_to_gen(&self.a);
        let b = bn_to_gen(&self.b);
        let c = bn_to_gen(&self.c);

        //  GEN qfi(GEN a, GEN b, GEN c) (assumes b^2 − 4ac < 0)
        unsafe { qfi(a, b, c) }
    }

    // construct BinaryQF from pari GEN encoded qfb
    pub fn pari_qf_to_qf(pari_qf: GEN) -> Self {
        // TODO: add check that GEN is indeed a qfb
        let a_string = pari_qf_comp_to_decimal_string(pari_qf, 1);
        let b_string = pari_qf_comp_to_decimal_string(pari_qf, 2);
        let c_string = pari_qf_comp_to_decimal_string(pari_qf, 3);

        let a: BigInt = BigInt::from_str_radix(&a_string, 10).unwrap();
        let b: BigInt = BigInt::from_str_radix(&b_string, 10).unwrap();
        let c: BigInt = BigInt::from_str_radix(&c_string, 10).unwrap();

        BinaryQF { a, b, c }
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut a_vec = BigInt::to_bytes(&self.a);
        let b_vec = BigInt::to_bytes(&self.b);
        let c_vec = BigInt::to_bytes(&self.c);
        a_vec.extend_from_slice(&b_vec[..]);
        a_vec.extend_from_slice(&c_vec[..]);
        a_vec
    }

    /// Takes point in reduced form and returns its compressed
    /// representation.
    ///
    /// Follows Algorithm 1 from [paper](https://eprint.iacr.org/2020/196.pdf).
    ///
    /// Returns `None` if Self is not in reduced form. Use
    /// [is_reduced](Self::is_reduced) to determine if it can be comressed
    /// and [reduce](Self::reduce) to find equivalent in reduced form
    /// for any BinaryQF.
    pub fn to_compressed(&self) -> Option<BinaryQFCompressed> {
        if !self.is_reduced() {
            return None;
        }

        // 1. (s, u, t) <- PartialXGCD(|a|, |b|, sqrt(|a|)
        let (_s, _u, mut t) = partial_xgcd(&self.a.abs(), &self.b.abs());
        // 2. if b < 0 then t <- -t
        if self.b < BigInt::zero() {
            t = -t
        }

        // 3. g <- gcd(a,t)
        let (g, _, _) = BigInt::egcd(&self.a, &t);
        // 4. a' <- a/g
        let a1 = &self.a / &g;
        // 5-8. if a = b then t' <- 0 else t' <- t/g
        let t1 = if self.a == self.b {
            BigInt::zero()
        } else {
            &t / &g
        };
        // 9. b0 <- b mod g
        let b0 = self.b.modulus(&g);
        // 10. ε <- [b >= 0]
        let e = self.b >= BigInt::zero();

        let delta = self.discriminant();
        Some(BinaryQFCompressed {
            a1,
            t1,
            g,
            b0,
            e,
            delta,
        })
    }

    pub fn from_compressed(compressed: BinaryQFCompressed) -> Option<Self> {
        Some(Self::binary_quadratic_form_disc(
            &ABDeltaTriple::from_compressed(compressed)?,
        ))
    }
}

impl ABDeltaTriple {
    pub fn from_compressed(compressed: BinaryQFCompressed) -> Option<Self> {
        let BinaryQFCompressed {
            a1,
            t1,
            g,
            b0,
            e,
            delta,
        } = compressed;

        // 1. a <- g * a'
        let a = &g * &a1;
        // 2. t <- g * t'
        let t = &g * &t1;
        // 3. if t = 0 then return (a,a)
        if t.is_zero() {
            return Some(Self {
                a: a.clone(),
                b: a,
                delta,
            });
        }
        // 4. x <- t^2 * ∆ (mod a)
        let t2 = BigInt::mod_mul(&t, &t, &a);
        let x = BigInt::mod_mul(&t2, &delta, &a);
        // 5. s <- sqrt(x)
        let s = x.sqrt();
        // 6. s' <- s/g
        let s1 = &s / &g;
        // 7. b' <- s' * t^−1 (mod a')
        let t_inv = BigInt::mod_inv(&t, &a1)?;
        let b1 = BigInt::mod_mul(&s1, &t_inv, &a1);
        // 8. b <- CRT((b', a'), (b0, g))
        let mut b: BigInt =
            chinese_reminder_theorem::chinese_remainder_theorem(&[b1, b0], &[a1, g])?;
        // 9. if ε = False then b <- −b (mod a)
        if !e {
            b = -b
        }
        // 10. return (a,b)
        Some(Self { a, b, delta })
    }
}

/// Takes a,b (a > b > 0), produces r,s,t such as `r = s * a + t * b` where `|r|,|t| < sqrt(a)`
fn partial_xgcd(a: &BigInt, b: &BigInt) -> (BigInt, BigInt, BigInt) {
    let mut r = (a.clone(), b.clone());
    let mut s = (BigInt::one(), BigInt::zero());
    let mut t = (BigInt::zero(), BigInt::one());

    let a_sqrt = a.sqrt();
    while r.1 > a_sqrt {
        let q = &r.0 / &r.1;
        let r1 = &r.0 - &q * &r.1;
        let s1 = &s.0 - &q * &s.1;
        let t1 = &t.0 - &q * &t.1;

        swap(&mut r.0, &mut r.1);
        r.1 = r1;
        swap(&mut s.0, &mut s.1);
        s.1 = s1;
        swap(&mut t.0, &mut t.1);
        t.1 = t1;
    }

    (r.1, s.1, t.1)
}

// helper functions:
// this function turns a bigint into GEN (native Pari type)
pub fn bn_to_gen(bn: &BigInt) -> GEN {
    let neg1 = if bn < &BigInt::zero() { -1 } else { 1 };
    let neg_bn: BigInt = if bn < &BigInt::zero() {
        -BigInt::one()
    } else {
        BigInt::one()
    };
    let bn: BigInt = bn * &neg_bn;

    let bn_len = bn.bit_length();
    let num_int_bound: usize;
    if bn_len % 8 == 0 {
        num_int_bound = bn_len / 8;
    } else {
        num_int_bound = bn_len / 8 + 1;
    }
    let size_int = 32;
    let two_bn = BigInt::from(2);
    let all_ones_32bits = two_bn.pow(size_int as u32) - BigInt::one();
    let mut array = [0u8; 4];
    let ints_vec = (0..num_int_bound)
        .map(|i| {
            let masked_valued_bn = (&bn & &all_ones_32bits << (i * size_int)) >> (i * size_int);

            let mut masked_value_bytes = BigInt::to_bytes(&masked_valued_bn);
            // padding if int has leading zero bytes
            let mut template = vec![0; 4 - masked_value_bytes.len()];
            template.extend_from_slice(&masked_value_bytes);
            masked_value_bytes = template;

            array.copy_from_slice(&masked_value_bytes[..]);

            u32::from_be_bytes(array) as i64
        })
        .collect::<Vec<i64>>();

    let mut i = 0;
    let mut gen = unsafe { mkintn(1i64, 0i64) };
    unsafe {
        while i < num_int_bound {
            let elem1 = mkintn(1i64, ints_vec[num_int_bound - i - 1]);
            let elem2 = shifti(gen, (size_int) as i64);
            gen = gadd(elem1, elem2);
            i += 1
        }

        if neg1 == -1 {
            gen = gneg(gen);
        }

        gen
    }
}

pub fn pari_qf_comp_to_decimal_string(pari_qf: GEN, index: usize) -> String {
    let comp = unsafe { compo(pari_qf, index as i64) };

    let comp_char_ptr = unsafe { GENtostr(comp) };
    let c_buf: *const c_char = comp_char_ptr;
    let c_str: &CStr = unsafe { CStr::from_ptr(c_buf) };
    let comp_str_slice: &str = c_str.to_str().unwrap();
    comp_str_slice.to_string()
}

#[cfg(test)]
mod tests {
    use std::str;

    use proptest::prelude::*;

    use super::*;
    use crate::curv::arithmetic::traits::Samplable;

    #[test]
    fn test_qf_to_pari_qf_to_qf() {
        unsafe {
            pari_init(10000000, 2);
        }
        let a: BigInt = BigInt::from_str_radix("1347310664179468558147371727982960102805371574927252724399119343247182932538452304549609704350360058405827948976558722087559341859252338031258062288910984654814255199874816496621961922792890687089794760104660404141195904459619180668507135317125790028783030121033883873501532619563806411495141846196437", 10).unwrap();

        let b = BigInt::from(2);
        let delta = -BigInt::from(3) * BigInt::from(201);
        let abd = ABDeltaTriple { a, b, delta };
        let pf = BinaryQF::binary_quadratic_form_disc(&abd);
        let pari_qf = pf.qf_to_pari_qf();
        let pf2 = BinaryQF::pari_qf_to_qf(pari_qf);
        assert_eq!(pf, pf2);
    }

    #[test]
    fn test_bn_to_gen_to_bn() {
        unsafe {
            pari_init(10000000, 2);
        }
        let test: BigInt = BigInt::sample(1600);
        let gen = bn_to_gen(&test);

        let char_ptr = unsafe { GENtostr(gen) };
        let c_buf: *const c_char = char_ptr;
        let c_str: &CStr = unsafe { CStr::from_ptr(c_buf) };
        let str_slice: &str = c_str.to_str().unwrap();
        let string_slice = str_slice.to_string();
        let test2: BigInt = BigInt::from_str_radix(&string_slice, 10).unwrap();

        assert_eq!(test, test2);
    }

    #[test]
    fn test_compose_exp() {
        unsafe {
            pari_init(10000000, 2);
        }
        let mut det: BigInt;

        det = -BigInt::sample(1600);
        while det.mod_floor(&BigInt::from(4)) != BigInt::one() {
            det = -BigInt::sample(1600);
        }
        let a_b_delta = ABDeltaTriple {
            a: BigInt::from(2),
            b: BigInt::from(1),
            delta: det,
        };
        let group = BinaryQF::binary_quadratic_form_disc(&a_b_delta);
        let x = BigInt::sample(100);
        let g = group.exp(&x).reduce();
        let gg1 = g.compose(&g).reduce();
        let gg2 = g.exp(&BigInt::from(2)).reduce();
        assert_eq!(gg1, gg2);
    }

    #[test]
    fn test_principal_exp() {
        unsafe {
            pari_init(10000000, 2);
        }
        let mut det: BigInt;

        det = -BigInt::sample(1600);
        while det.mod_floor(&BigInt::from(4)) != BigInt::one() {
            det = -BigInt::sample(1600);
        }
        let f = BinaryQF::binary_quadratic_form_principal(&det);
        let x = BigInt::sample(100);
        let f_exp = f.exp(&x);
        assert_eq!(f, f_exp);
    }

    proptest::proptest! {
        #[test]
        fn fuzz_partial_xgcd(a in any::<u32>(), b in any::<u32>()) {
            proptest::prop_assume!(a > b && b > 0);
            test_partial_xgcd(BigInt::from(a), BigInt::from(b))
        }
        #[test]
        fn fuzz_compression(d in 1u32..) {
            let delta = BigInt::from(d) * BigInt::from(-4) + BigInt::one();
            test_compression(delta)
        }
    }

    fn test_partial_xgcd(a: BigInt, b: BigInt) {
        let (r, s, t) = partial_xgcd(&a, &b);
        println!("r={}, s={}, t={}", r, s, t);

        // We expect that r = a * s + b * t
        assert_eq!(r, &a * &s + &b * &t);

        // We expect both |r| and |t| to be less than sqrt(a)
        let a_sqrt = a.sqrt();
        assert!(
            r.abs() < a_sqrt,
            "r is not less than sqrt(a), diff = {}",
            &r - &a_sqrt
        );
        assert!(
            t.abs() < a_sqrt,
            "t is not less than sqrt(a), diff = {}",
            &t - &a_sqrt
        );
    }

    fn test_compression(delta: BigInt) {
        let uncompressed = BinaryQF::binary_quadratic_form_principal(&delta).reduce();
        let compressed = uncompressed.to_compressed().expect("failed to compress");
        let uncompressed2 = BinaryQF::from_compressed(compressed).expect("failed to decompress");

        assert_eq!(uncompressed, uncompressed2);
    }
}
