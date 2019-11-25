pub mod cl_dl_lcm;
pub mod dl_cl;
pub mod poe;
pub mod polynomial_comm;

use curv::BigInt;
use std::error::Error;
use std::fmt;

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
