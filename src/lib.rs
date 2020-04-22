#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(dead_code)]

include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

extern crate libc;
#[macro_use]
extern crate serde_derive;
extern crate curv;
extern crate serde;
extern crate serde_json;
use crate::curv::arithmetic::traits::Converter;
use curv::BigInt;
use libc::c_char;
use std::ffi::CStr;
use std::ops::Neg;
use std::str;

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
        if self.is_normal() && self.a <= self.c && !(self.a == self.c && self.b < BigInt::zero()) {
            return true;
        } else {
            return false;
        }
    }

    pub fn normalize(&self) -> Self {
        // assume delta<0 and a>0
        let a_sub_b: BigInt = &self.a - &self.b;
        let s_f = a_sub_b.div_floor(&(BigInt::from(2) * &self.a));
        let binary_qf = BinaryQF {
            a: self.a.clone(),
            b: &self.b + BigInt::from(2) * &s_f * &self.a,
            c: &self.a * &s_f.pow(2) + &self.b * &s_f + &self.c,
        };

        binary_qf
    }

    pub fn is_normal(&self) -> bool {
        if self.b <= self.a && self.b > -self.a.clone() {
            return true;
        } else {
            return false;
        }
    }
    pub fn primeform(quad_disc: &BigInt, q: &BigInt) -> Self {
        let quad_disc_gen = bn_to_gen(&quad_disc);

        let q_gen = bn_to_gen(&q);

        let pf = unsafe { primeform(quad_disc_gen, q_gen, 3i64) };

        let bqf = BinaryQF::pari_qf_to_qf(pf);

        let bqf_norm = bqf.normalize();
        bqf_norm
    }

    pub fn compose(&self, qf2: &BinaryQF) -> Self {
        assert_eq!(self.discriminant(), qf2.discriminant());
        let qf_pari_a = self.qf_to_pari_qf();

        let qf_pari_b = qf2.qf_to_pari_qf();

        let qf_pari_c = unsafe { qfbcompraw(qf_pari_a, qf_pari_b) };

        let qf_c = BinaryQF::pari_qf_to_qf(qf_pari_c);

        qf_c
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
        let h = qf_new.normalize();

        h
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

        let mut v = unsafe { std::mem::MaybeUninit::uninit().assume_init() };
        let pari_qf_exp = unsafe { nupow(pari_qf, pari_n, &mut v) };
        let qf_exp = BinaryQF::pari_qf_to_qf(pari_qf_exp);
        qf_exp
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
        let qf = BinaryQF::binary_quadratic_form_disc(&abdelta);
        qf
    }

    // compute (p^(2),p,-)^k in class group of disc. delta
    pub fn expo_f(p: &BigInt, delta: &BigInt, k: &BigInt) -> BinaryQF {
        if k == &BigInt::zero() {
            return BinaryQF::binary_quadratic_form_principal(delta);
        }
        let mut k_inv = k.invert(p).unwrap();
        if k_inv.mod_floor(&BigInt::from(2)) == BigInt::zero() {
            k_inv = k_inv - p;
        };
        let k_inv_p = k_inv * p;
        let abdelta = ABDeltaTriple {
            a: p * p,
            b: k_inv_p,
            delta: delta.clone(),
        };
        let qf = BinaryQF::binary_quadratic_form_disc(&abdelta);
        qf
    }

    pub fn discrete_log_f(p: &BigInt, delta: &BigInt, c: &BinaryQF) -> BigInt {
        let principal_qf = BinaryQF::binary_quadratic_form_principal(delta);
        if c == &principal_qf {
            return BigInt::zero();
        } else {
            let Lk = c.b.div_floor(p);
            let Lk_inv = Lk.invert(p).unwrap();
            return Lk_inv;
        }
    }

    //we construct a pari qf from qf
    pub fn qf_to_pari_qf(&self) -> GEN {
        let a = bn_to_gen(&self.a);
        let b = bn_to_gen(&self.b);
        let c = bn_to_gen(&self.c);
        let qf_pari = unsafe { qfi(a, b, c) };
        //  GEN qfi(GEN a, GEN b, GEN c) (assumes b^2 − 4ac < 0)
        qf_pari
    }

    // construct BinaryQF from pari GEN encoded qfb
    pub fn pari_qf_to_qf(pari_qf: GEN) -> Self {
        // TODO: add check that GEN is indeed a qfb
        let a_string = pari_qf_comp_to_decimal_string(pari_qf, 1);
        let b_string = pari_qf_comp_to_decimal_string(pari_qf, 2);
        let c_string = pari_qf_comp_to_decimal_string(pari_qf, 3);

        let a: BigInt = str::parse(&a_string).unwrap();
        let b: BigInt = str::parse(&b_string).unwrap();
        let c: BigInt = str::parse(&c_string).unwrap();

        BinaryQF { a, b, c }
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut a_vec = BigInt::to_vec(&self.a);
        let b_vec = BigInt::to_vec(&self.b);
        let c_vec = BigInt::to_vec(&self.c);
        a_vec.extend_from_slice(&b_vec[..]);
        a_vec.extend_from_slice(&c_vec[..]);
        a_vec
    }
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
            let masked_valued_bn =
                (bn.clone() & all_ones_32bits.clone() << (i * size_int)) >> (i * size_int);

            let mut masked_value_bytes = BigInt::to_vec(&masked_valued_bn);
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
            i = i + 1
        }

        if neg1 == -1 {
            gen = gneg(gen);
        }

        return gen;
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
    use super::*;
    extern crate libc;
    use crate::curv::arithmetic::traits::Samplable;
    use std::str;

    #[test]
    fn test_qf_to_pari_qf_to_qf() {
        unsafe {
            pari_init(10000000, 2);
        }
        let a: BigInt = str::parse("1347310664179468558147371727982960102805371574927252724399119343247182932538452304549609704350360058405827948976558722087559341859252338031258062288910984654814255199874816496621961922792890687089794760104660404141195904459619180668507135317125790028783030121033883873501532619563806411495141846196437").unwrap();

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
        let test2: BigInt = str::parse(&string_slice).unwrap();

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
}
