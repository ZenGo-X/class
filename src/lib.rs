#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]

include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

extern crate libc;
extern crate paillier;
use libc::c_long;
extern crate curv;
use crate::curv::arithmetic::traits::Converter;
use curv::BigInt;
use libc::c_char;
use std::ffi::CStr;
use std::ops::Neg;
use std::ptr;
use std::str;

pub mod primitives;
/*
#[link(name = "pari")]
extern {

    fn primeform(x: GEN, p: GEN, prec: long ) -> GEN;
    fn snappy_max_compressed_length(source_length: size_t) -> size_t;
}
*/
#[derive(PartialEq, Eq, Clone, Debug)]
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

pub struct Matrix22 {
    pub a11: BigInt,
    pub a12: BigInt,
    pub a21: BigInt,
    pub a22: BigInt,
}

impl Matrix22 {
    pub fn mul(&self, another: &Self) -> Self {
        Matrix22 {
            a11: &self.a11 * &another.a11 + &self.a12 * &another.a21,
            a12: &self.a11 * &another.a12 + &self.a12 * &another.a22,
            a21: &self.a21 * &another.a11 + &self.a22 * &another.a21,
            a22: &self.a21 * &another.a12 + &self.a22 * &another.a22,
        }
    }
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

    pub fn normalize(&self) -> (Self, Matrix22) {
        // assume delta<0 and a>0
        let a_sub_b: BigInt = &self.a - &self.b;
        let s_f = a_sub_b.div_floor(&(BigInt::from(2) * &self.a));
        let binary_qf = BinaryQF {
            a: self.a.clone(),
            b: &self.b + BigInt::from(2) * &s_f * &self.a,
            c: &self.a * &s_f.pow(2) + &self.b * &s_f + &self.c,
        };
        let matrix = Matrix22 {
            a11: BigInt::one(),
            a12: BigInt::zero(),
            a21: s_f,
            a22: BigInt::one(),
        };

        (binary_qf, matrix)
    }

    pub fn is_normal(&self) -> bool {
        if self.b < self.a && self.b > -self.a.clone() {
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

        let (bqf_norm, matrix) = bqf.normalize();
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

    pub fn rho(&self) -> (Self, Matrix22) {
        let qf_new = BinaryQF {
            a: self.c.clone(),
            b: self.b.clone().neg(),
            c: self.a.clone(),
        };
        let (h, N) = qf_new.normalize();
        // [[0,-1] [1, 0]] * N
        let N_new = Matrix22 {
            a11: N.a21.clone(),
            a12: N.a22.clone(),
            a21: N.a11.clone().neg(),
            a22: N.a21.clone().neg(),
        };
        (h, N_new)
    }

    pub fn reduce(&self) -> (Self, Matrix22) {
        let mut M: Matrix22;
        let mut h: BinaryQF;
        let (h_new, M_new) = self.normalize();
        h = h_new;
        M = M_new;
        while !h.is_reduced() {
            let (h_new, M_new) = h.rho();
            M = M.mul(&M_new);
            h = h_new;
        }
        (h, M)
    }

    pub fn exp(&self, n: &BigInt) -> BinaryQF {
        let pari_qf = self.qf_to_pari_qf();
        let pari_n = bn_to_gen(n);

        let mut v = unsafe { std::mem::uninitialized() };
        let pari_qf_exp = unsafe { nupow(pari_qf, pari_n, &mut v) };
        let qf_exp = BinaryQF::pari_qf_to_qf(pari_qf_exp);
        qf_exp
    }

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

        let a = decimal_string_to_bn(a_string);
        let b = decimal_string_to_bn(b_string);
        let c = decimal_string_to_bn(c_string);

        BinaryQF { a, b, c }
    }
}
// helper functions:
// this function turns a 512bit bigint into GEN (native Pari type) //TODO: make the bn variable size
pub fn bn_to_gen(bn: &BigInt) -> GEN {
    // we do not test for bit length = 576 because there might be leading zeros.
    // therefore we just pad with 0 bits to get bit-length - 576. or cut the first 576bits
    let neg1: i64 = if bn < &BigInt::zero() { -1 } else { 1 };
    let neg_bn: BigInt = if bn < &BigInt::zero() {
        -BigInt::one()
    } else {
        BigInt::one()
    };
    let bn = bn * &neg_bn;

    let num_ints = 36;
    let size_int = 32;
    let two_bn = BigInt::from(2);
    let all_ones_32bits = two_bn.pow(32) - BigInt::one();
    let mut array = [0u8; 4];
    let mut ints_vec = (0..num_ints)
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

    unsafe {
        let mut gen = mkintn(
            num_ints as i64,
            ints_vec[35],
            ints_vec[34],
            ints_vec[33],
            ints_vec[32],
            ints_vec[31],
            ints_vec[30],
            ints_vec[29],
            ints_vec[28],
            ints_vec[27],
            ints_vec[26],
            ints_vec[25],
            ints_vec[24],
            ints_vec[23],
            ints_vec[22],
            ints_vec[21],
            ints_vec[20],
            ints_vec[19],
            ints_vec[18],
            ints_vec[17],
            ints_vec[16],
            ints_vec[15],
            ints_vec[14],
            ints_vec[13],
            ints_vec[12],
            ints_vec[11],
            ints_vec[10],
            ints_vec[9],
            ints_vec[8],
            ints_vec[7],
            ints_vec[6],
            ints_vec[5],
            ints_vec[4],
            ints_vec[3],
            ints_vec[2],
            ints_vec[1],
            ints_vec[0],
        );
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

//TODO: use str::parse
pub fn decimal_string_to_bn(dec_string: String) -> BigInt {
    let mut char_iter = dec_string.chars();
    let mut negative_flag = 1;
    let ten = BigInt::from(10);
    match char_iter.position(|minus| &minus.to_string() == "-") {
        Some(x) => {
            if x == 0 {
                negative_flag = -1;
            }
        }
        None => {
            char_iter = dec_string.chars();
        }
    }

    let bn = char_iter.fold(BigInt::zero(), |acc, x| {
        let res = acc * &ten + BigInt::from(x.to_digit(10).unwrap());
        res
    });
    bn * BigInt::from(negative_flag)
}

#[link(name = "pari")]
extern "C" {
    fn stoi(s: i64) -> GEN;
    fn addii(x: GEN, y: GEN) -> GEN;
    fn vecslice(A: GEN, j1: i64, j2: i64) -> GEN;
    fn mpcmp(x: GEN, y: GEN) -> GEN;
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::mem;
    use std::ptr;
    use std::ptr::null;
    extern crate libc;
    use libc::c_char;
    use std::ffi::CStr;
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
    fn test_bn_to_gen_to_bn() {}
}
