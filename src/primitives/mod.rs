pub mod cl_dl_lcm;
pub mod poe;
pub mod polynomial_comm;
pub mod vdf;

use crate::curv::cryptographic_primitives::hashing::traits::Hash;
use crate::BinaryQF;
use curv::cryptographic_primitives::hashing::hash_sha256::HSha256;
use curv::cryptographic_primitives::hashing::hmac_sha512::HMacSha512;
use curv::cryptographic_primitives::hashing::traits::KeyedHash;
use curv::BigInt;
use paillier::keygen;
use std::error::Error;
use std::fmt;
use std::ops::Shl;

#[derive(Debug, Clone, Copy)]
pub struct ProofError;

impl fmt::Display for ProofError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "ProofError")
    }
}

impl Error for ProofError {
    fn description(&self) -> &str {
        "Error while verifying"
    }
}

#[derive(Copy, PartialEq, Eq, Clone, Debug)]
pub enum ErrorReason {
    OpenCommError,
    EvalError,
    VDFVerifyError,
    SetupError,
    PoEError,
}

//TODO: improve approximation
fn numerical_log(x: &BigInt) -> BigInt {
    let mut aip1: BigInt;
    let mut bip1: BigInt;
    let two = BigInt::from(2);
    let mut ai = (BigInt::one() + x).div_floor(&two);
    let mut bi = x.sqrt();
    let mut k = 0;
    while k < 1000 {
        k = k + 1;
        aip1 = (&ai + &bi).div_floor(&two);
        bip1 = (ai * bi).sqrt();
        ai = aip1;
        bi = bip1;
    }

    let log = two * (x - &BigInt::one()).div_floor(&(ai + bi));
    log
}

pub fn hash_to_prime(u: &BinaryQF, w: &BinaryQF) -> BigInt {
    let mut candidate = HSha256::create_hash(&[&u.a, &u.b, &u.c, &w.a, &w.b, &w.c]);

    while !keygen::is_prime(&candidate) {
        candidate = candidate + BigInt::from(1);
    }
    candidate
}

fn prng(seed: &BigInt, i: usize, bitlen: usize) -> BigInt {
    let i_bn = BigInt::from(i as i32);
    let mut res = HMacSha512::create_hmac(&i_bn, &vec![seed]);
    let mut tmp: BigInt = res.clone();
    let mut res_bit_len = res.bit_length();
    while res_bit_len < bitlen {
        tmp = HMacSha512::create_hmac(&i_bn, &vec![&tmp]);
        res = &res.shl(res_bit_len.clone()) + &tmp;
        res_bit_len = res.bit_length();
    }
    // prune to get |res| = bitlen
    res >> (res_bit_len - &bitlen)
}
