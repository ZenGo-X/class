use crate::pari_init;
use crate::primitives::hash_to_prime;
use crate::primitives::is_prime;
use crate::primitives::prng;
use crate::primitives::ErrorReason;
use crate::ABDeltaTriple;
use crate::BinaryQF;
use curv::arithmetic::traits::*;
use curv::BigInt;

/// Wesolowski VDF, based on https://eprint.iacr.org/2018/712.pdf.
/// Original paper: https://eprint.iacr.org/2018/623.pdf
///
pub struct VDF {
    pub x: BigInt,
    pub y: BinaryQF,
    pub pi: BinaryQF,
    pub t: BigInt,
    a_b_delta: ABDeltaTriple,
}

impl VDF {
    pub fn setup(security_param: usize, x: &BigInt) -> ABDeltaTriple {
        let mut disc: BigInt;

        disc = -BigInt::sample(security_param); // TODO: double check 1600 bits determinant should provide 120 bit security
                                                // based on "Survey on IQ cryptography" 3.2
        while disc.mod_floor(&BigInt::from(4)) != BigInt::one() || !is_prime(&(-&disc)) {
            disc = -BigInt::sample(security_param);
        }

        unsafe {
            pari_init(1000000000, 2);
        }
        //first line: g <- H_G(x). We will use x to seed a prng and use the prng to choose random
        // a and b.
        let (a, b) = h_g(&disc, x);
        ABDeltaTriple { a, b, delta: disc }
    }

    //algorithm 3 from https://eprint.iacr.org/2018/623.pdf
    pub fn eval(a_b_delta: &ABDeltaTriple, x: &BigInt, t: &BigInt) -> Self {
        unsafe {
            pari_init(1000000000, 2);
        }

        let g = BinaryQF::binary_quadratic_form_disc(a_b_delta).reduce();
        let mut y = g.clone();
        let mut i = BigInt::zero();

        while &i < t {
            y = y.compose(&y).reduce();
            i += BigInt::one();
        }
        let l = hash_to_prime(&g, &y);

        //algorithm 4 from https://eprint.iacr.org/2018/623.pdf
        // long division TODO: consider alg 5 instead
        let mut i = BigInt::zero();
        let mut b: BigInt;
        let mut r = BigInt::one();
        let mut r2: BigInt;
        let two = BigInt::from(2);
        let mut pi = BinaryQF::binary_quadratic_form_principal(&a_b_delta.delta);

        while &i < t {
            r2 = &r * &two;
            b = r2.div_floor(&l);
            r = r2.mod_floor(&l);
            pi = pi.exp(&two).compose(&g.exp(&b)).reduce();
            i += BigInt::one();
        }

        VDF {
            x: x.clone(),
            y,
            pi,
            t: t.clone(),
            a_b_delta: a_b_delta.clone(),
        }
    }

    //algorithm 2 from https://eprint.iacr.org/2018/623.pdf
    pub fn verify(&self) -> Result<(), ErrorReason> {
        unsafe {
            pari_init(1000000000, 2);
        }

        let g = BinaryQF::binary_quadratic_form_disc(&self.a_b_delta).reduce();

        // test that g,y are elements of the class : https://eprint.iacr.org/2018/712.pdf 2.1 line 0
        if g.discriminant() != self.a_b_delta.delta
            || self.y.discriminant() != self.a_b_delta.delta
            || self.pi.discriminant() != self.a_b_delta.delta
        {
            return Err(ErrorReason::VDFVerifyError);
        }
        let l = hash_to_prime(&g, &self.y);

        let r = BigInt::mod_pow(&BigInt::from(2), &self.t, &l);
        let pi_l_g_r = self.pi.exp(&l).compose(&g.exp(&r)).reduce();

        match pi_l_g_r == self.y {
            true => Ok(()),
            false => Err(ErrorReason::VDFVerifyError),
        }
    }
}

/// helper function H_G(x)
/// Claudio algorithm:
/// 1) i = 0,
/// 2) r = prng(x,i)
/// 3) b = 2r + 1 // guarantee division by 4 later
/// 4) u = (b^2 - delta^2) / 4   // = ac
/// 5) choose small c at random and check if u/c is integral
/// 6) if true: take a = u/c
/// 7) if false : i++; goto 2.
fn h_g(disc: &BigInt, x: &BigInt) -> (BigInt, BigInt) {
    let mut i = 0;
    let two = BigInt::from(2);
    let max = BigInt::from(20);
    let mut b = &two * prng(x, i, disc.bit_length()) + BigInt::one();
    let mut c = two.clone();
    let mut b2_minus_disc: BigInt = b.pow(2) - disc;
    let four = BigInt::from(4);
    let mut u = b2_minus_disc.div_floor(&four);
    while u.mod_floor(&c) != BigInt::zero() {
        b = &two * prng(x, i, disc.bit_length()) + BigInt::one();
        b2_minus_disc = b.pow(2) - disc;
        u = b2_minus_disc.div_floor(&four);
        i += 1;
        c = (&c.next_prime()).mod_floor(&max);
    }
    let a = u.div_floor(&c);
    (a, b)
}

#[cfg(test)]
mod tests {
    use super::VDF;
    use crate::curv::arithmetic::traits::Samplable;
    use curv::BigInt;
    use std::time::Instant;

    #[test]
    fn test_vdf_valid_proof() {
        let sec = 1600;
        let t = BigInt::sample(10); // TODO: make sure T is not too big to avoid memory overflow
        let x = BigInt::from(10);
        let a_b_delta = VDF::setup(sec, &x);

        let mut i = 0;
        while i < 10 {
            let start = Instant::now();
            let vdf_out_proof = VDF::eval(&a_b_delta, &x, &t);
            let duration1 = start.elapsed();
            let start = Instant::now();
            let res = vdf_out_proof.verify();
            let duration2 = start.elapsed();
            i += 1;

            println!("eval time: {:?}", duration1);
            println!("verify time: {:?}", duration2);
            // results for random t<1000:
            //eval time: 2.121114598s
            //verify time: 5.115038ms
            assert!(res.is_ok());
        }
    }

    #[test]
    #[should_panic]
    fn test_vdf_wrong_proof() {
        let sec = 1600;
        let t = BigInt::sample(10);
        let x = BigInt::from(10);
        let a_b_delta = VDF::setup(sec, &x);

        let mut vdf_out_proof = VDF::eval(&a_b_delta, &x, &t);
        println!("before: {:?}", vdf_out_proof.y);

        vdf_out_proof.y = vdf_out_proof.y.exp(&BigInt::from(3));
        println!("after: {:?}", vdf_out_proof.y);
        let res = vdf_out_proof.verify();

        assert!(res.is_ok());
    }
}
