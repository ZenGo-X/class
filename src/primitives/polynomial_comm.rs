use super::ErrorReason;
use crate::pari_init;
use crate::primitives::is_prime;
use crate::primitives::poe::PoEProof;
use crate::ABDeltaTriple;
use crate::BinaryQF;
use curv::arithmetic::traits::*;
use curv::cryptographic_primitives::hashing::{Digest, DigestExt};
use curv::elliptic::curves::{secp256_k1::Secp256k1, Scalar};
use curv::BigInt;
use sha2::Sha256;

/// Polynomial commitment as given in the paper: Transparent SNARKs from DARK Compilers
/// (https://eprint.iacr.org/2019/1229.pdf), subsection 4.2 and 4.3
/// The following algorithms are implemented:
/// Setup: generates public parameters
/// Commit: to commit to a polynomial
/// Open: open and verify a commitment
/// Encode: stand alone code to encode a polynomial as an integer
/// Decode: converts integer to a unique polynomial
/// Eval_prover: NI proof that y = f(z) for a committed polynomial f()
/// Eval_verify: NI verifier for eval_proof.
///
///

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct PP {
    pub disc: BigInt,
    pub g: BinaryQF,
    pub q: BigInt,
    pub p: BigInt,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct PolyComm {
    pub c: BinaryQF,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct NiEvalProof {
    c_l_vec: Vec<BinaryQF>,
    c_r_vec: Vec<BinaryQF>,
    y_l_vec: Vec<BigInt>,
    y_r_vec: Vec<BigInt>,
    poe_proof_vec: Vec<PoEProof>,
    f_const: BigInt,
    d: usize,
    b: BigInt,
}

impl PolyComm {
    // d is the rank of the polynomial,
    pub fn setup(d_max: &BigInt) -> PP {
        unsafe { pari_init(100000000000, 2) };

        // TODO: use standardize setup for sampling random element
        // choose determinant with 1600 bits, which is equivalent to 3072 bit RSA. That I believe is 120bit security now
        let mut disc: BigInt;

        disc = -BigInt::sample(1600);

        // based on "Survey on IQ cryptography" 3.2
        while disc.mod_floor(&BigInt::from(4)) != BigInt::one() || !is_prime(&(-&disc)) {
            disc = -BigInt::sample(1600);
        }
        //  let group = BinaryQF::binary_quadratic_form_principal(&det);

        // sample random number to get a random group element.

        //  let random = BigInt::sample(256);
        //  let g = group.exp(&random);
        let g = pick_random_element(&disc);

        let bound = 3 * (d_max + BigInt::one()).bit_length() as u32 + 1;

        let p = Scalar::<Secp256k1>::group_order();
        let q = p.pow(bound);
        PP {
            disc,
            g,
            q,
            p: p.clone(),
        }
    }

    pub fn commit(pp: &PP, coef_vec: &[Scalar<Secp256k1>]) -> (PolyComm, BigInt) {
        unsafe { pari_init(100000000000, 2) };

        let two = BigInt::from(2);
        let p_minus1_half = (&pp.p - &BigInt::one()).div_floor(&two);
        let coef_vec_int = (0..coef_vec.len())
            .map(|i| {
                let mut coef_i_bn = coef_vec[i].to_bigint();
                if coef_i_bn > p_minus1_half {
                    coef_i_bn -= &pp.p;
                }
                coef_i_bn
            })
            .collect::<Vec<BigInt>>();
        // transform to Z :
        let mut coef_vec_rev = coef_vec_int.iter().rev();
        let head = coef_vec_rev.next().unwrap();
        let tail = coef_vec_rev;
        let f_q = tail.fold(head.clone(), |acc, x| x + &acc * &pp.q);

        let c = pp.g.exp(&f_q);
        (PolyComm { c }, f_q)
    }

    pub fn open(self, pp: &PP, coef_vec: &[Scalar<Secp256k1>]) -> Result<(), ErrorReason> {
        unsafe { pari_init(100000000000, 2) };
        let two = BigInt::from(2);
        let p_minus1_half = (&pp.p - &BigInt::one()).div_floor(&two);
        let coef_vec_int = (0..coef_vec.len())
            .map(|i| {
                let mut coef_i_bn = coef_vec[i].to_bigint();
                if coef_i_bn > p_minus1_half {
                    coef_i_bn -= &pp.p;
                }
                coef_i_bn
            })
            .collect::<Vec<BigInt>>();
        // transform to Z :
        let mut coef_vec_rev = coef_vec_int.iter().rev();
        let head = coef_vec_rev.next().unwrap();
        let tail = coef_vec_rev;
        let f_q = tail.fold(head.clone(), |acc, x| x + &acc * &pp.q);
        let c = pp.g.exp(&f_q);
        match c == self.c {
            true => Ok(()),
            false => Err(ErrorReason::OpenCommError),
        }
    }

    pub fn encode(p: &BigInt, q: &BigInt, coef_vec: &[Scalar<Secp256k1>]) -> BigInt {
        // notation change to fit the paper:
        // transform the coefficients to integer coefficients bounded [-p/2,p/2]
        let coef_vec_int = (0..coef_vec.len())
            .map(|i| coef_vec[i].to_bigint() - &p.div_floor(&BigInt::from(2)))
            .collect::<Vec<BigInt>>();
        // transform to Z :

        let mut coef_vec_rev = coef_vec_int.iter().rev();
        let head = coef_vec_rev.next().unwrap();
        let tail = coef_vec_rev;

        tail.fold(head.clone(), |acc, x| x + acc * q)
    }

    pub fn decode(p: &BigInt, q: &BigInt, y: &BigInt) -> Vec<Scalar<Secp256k1>> {
        let one = BigInt::one();
        let p_half = p.div_floor(&BigInt::from(2));
        let bits_in_y = BigInt::from(y.bit_length() as u32);
        let bits_in_q = BigInt::from(q.bit_length() as u32);
        let mut d: BigInt = one.clone();
        while &d * &bits_in_q < bits_in_y {
            d += &one
        }

        let mut coef_vec: Vec<Scalar<Secp256k1>> = Vec::new();
        let mut q_k = BigInt::one();
        let two = BigInt::from(2);
        let one = BigInt::from(1);
        let s_minus_1 = BigInt::zero();
        let mut s_0 = y.mod_floor(q);
        if s_0 > q.div_floor(&two) {
            s_0 = q - &s_0;
            s_0 = -s_0 + &p_half;
        } else {
            s_0 = &s_0 + &p_half;
        }
        q_k *= q;

        let f_0: BigInt = s_0 - s_minus_1;

        coef_vec.push(Scalar::<Secp256k1>::from(&f_0));
        if d == one {
            return coef_vec;
        }
        while d > one {
            let mut case = 0;
            let mut s_k_minus_1 = y.mod_floor(&q_k);
            if s_k_minus_1 > q_k.div_floor(&two) {
                s_k_minus_1 = &q_k - &s_k_minus_1;
                case += 1;
            } else {
                case += 10;
            }
            let q_k_plus_1 = &q_k * q;
            let mut s_k = y.mod_floor(&q_k_plus_1);
            if s_k > q_k_plus_1.div_floor(&two) {
                s_k = &q_k_plus_1 - &s_k;
                case += 100;
            } else {
                case += 1000;
            }
            let mut f_k: BigInt = (s_k - s_k_minus_1).div_floor(&q_k);

            match case {
                101 => f_k = -&f_k + &p_half,
                1001 => f_k = &f_k + &p_half + &one,
                110 => f_k = -&f_k + &p_half - &one,
                1010 => f_k = &f_k + &p_half,
                _ => println!("error"), // TODO: return an error
            };

            coef_vec.push(Scalar::<Secp256k1>::from(&f_k));
            q_k = q_k_plus_1;
            d -= &one;
        }
        coef_vec
    }

    pub fn eval_prove(
        &self,
        pp: &PP,
        z: &Scalar<Secp256k1>,
        y: &Scalar<Secp256k1>,
        coef_vec: &[Scalar<Secp256k1>],
    ) -> NiEvalProof {
        unsafe { pari_init(100000000000, 2) };

        let d = coef_vec.len() - 1; //TODO: make bigint, check d >=0
                                    //step 2:
        let two = BigInt::from(2);
        let p_minus1_half = (&pp.p - &BigInt::one()).div_floor(&two);
        let mut coef_vec_int = (0..coef_vec.len())
            .map(|i| {
                let mut coef_i_bn = coef_vec[i].to_bigint();
                if coef_i_bn > p_minus1_half {
                    coef_i_bn -= &pp.p;
                }

                coef_i_bn
            })
            .collect::<Vec<BigInt>>();

        PolyComm::eval_bounded_prove(&self.c, pp, z, y, d, p_minus1_half, &mut coef_vec_int[..])
    }

    pub fn eval_bounded_prove(
        c: &BinaryQF,
        pp: &PP,
        z: &Scalar<Secp256k1>,
        y: &Scalar<Secp256k1>,
        d: usize,
        b: BigInt,
        coef_vec: &mut [BigInt],
    ) -> NiEvalProof {
        let mut c_l_vec: Vec<BinaryQF> = Vec::new();
        let mut c_r_vec: Vec<BinaryQF> = Vec::new();
        let mut y_l_vec: Vec<BigInt> = Vec::new();
        let mut y_r_vec: Vec<BigInt> = Vec::new();
        let mut poe_proof_vec: Vec<PoEProof> = Vec::new();

        if d == 0 {
            let proof = NiEvalProof {
                c_l_vec,
                c_r_vec,
                y_l_vec,
                y_r_vec,
                poe_proof_vec,
                f_const: coef_vec[0].clone(),
                d,
                b,
            };
            return proof;
        }

        if (d + 1) % 2 == 1 {
            let d_prime = d + 1;
            let c_prime = c.exp(&pp.q);
            let y_prime = y * z;
            let b_prime = &b * BigInt::from(d as u32);

            let mut coef_vec = coef_vec.to_vec();
            coef_vec.reverse();
            coef_vec.push(BigInt::zero());
            coef_vec.reverse();

            let eval_proof = Self::eval_bounded_prove(
                &c_prime,
                pp,
                z,
                &y_prime,
                d_prime,
                b_prime,
                &mut coef_vec[..],
            );
            y_l_vec.extend_from_slice(&eval_proof.y_l_vec[..]);
            y_r_vec.extend_from_slice(&eval_proof.y_r_vec[..]);
            c_l_vec.extend_from_slice(&eval_proof.c_l_vec[..]);
            c_r_vec.extend_from_slice(&eval_proof.c_r_vec[..]);
            poe_proof_vec.extend_from_slice(&eval_proof.poe_proof_vec[..]);

            let proof = NiEvalProof {
                y_l_vec,
                y_r_vec,
                c_l_vec,
                c_r_vec,
                poe_proof_vec,
                f_const: eval_proof.f_const.clone(),
                d,
                b,
            };
            return proof;
        }

        //step 12
        let d_prime = (d + 1) / 2 - 1;
        //step 13
        let f_l_coef = &mut coef_vec[0..d_prime + 1].to_vec();
        let f_r_coef = &mut coef_vec[d_prime + 1..].to_vec();
        //step 14

        let mut f_l_coef_rev = f_l_coef.iter().rev();
        let head = f_l_coef_rev.next().unwrap();
        let tail = f_l_coef_rev;
        let z_bn = z.to_bigint();
        let y_l = tail.fold(head.clone(), |acc, x| x + &acc * &z_bn);

        let mut f_r_coef_rev = f_r_coef.iter().rev();
        let head = f_r_coef_rev.next().unwrap();
        let tail = f_r_coef_rev;
        let y_r = tail.fold(head.clone(), |acc, x| x + &acc * &z_bn);

        //step 15
        let mut f_l_coef_rev = f_l_coef.iter().rev();
        let head = f_l_coef_rev.next().unwrap();
        let tail = f_l_coef_rev;
        let f_l_q = tail.fold(head.clone(), |acc, x| x + &acc * &pp.q);

        let mut f_r_coef_rev = f_r_coef.iter().rev();
        let head = f_r_coef_rev.next().unwrap();
        let tail = f_r_coef_rev;
        let f_r_q = tail.fold(head.clone(), |acc, x| x + &acc * &pp.q);

        let c_l = pp.g.exp(&f_l_q).reduce();
        let c_r = pp.g.exp(&f_r_q).reduce();

        //step18
        let q_pow_d_prime_plus1 = pp.q.pow((d_prime + 1) as u32);
        let c_l_inverse = c_l.inverse();
        let c_over_c_l = c_l_inverse.compose(c).reduce();
        let poe_proof = PoEProof::prove(&q_pow_d_prime_plus1, &c_r, &c_over_c_l);

        //step 19
        // alpha = H(y_l ||y_r) for Fiat-Shamir
        let alpha = Sha256::new()
            .chain_bigint(&y_l)
            .chain_bigint(&y_r)
            .result_bigint();
        let mut alpha = alpha.mod_floor(&pp.p);
        if alpha > (&pp.p - BigInt::one()).div_floor(&BigInt::from(2)) {
            alpha -= &pp.p;
        }

        //step 20
        let y_prime: BigInt = &alpha * &y_l + &y_r;
        let y_prime_fe = Scalar::<Secp256k1>::from(&y_prime);
        let c_prime = c_l.exp(&alpha).compose(&c_r).reduce();
        let b_prime = &b * ((&pp.p + BigInt::one()).div_floor(&BigInt::from(2)));
        //step 21
        let mut coef_vec_int_prime = (0..f_l_coef.len())
            .map(|i| &f_l_coef[i] * &alpha + &f_r_coef[i])
            .collect::<Vec<BigInt>>();

        y_l_vec.push(y_l);
        y_r_vec.push(y_r);
        c_l_vec.push(c_l);
        c_r_vec.push(c_r);
        poe_proof_vec.push(poe_proof);

        //step 22
        let eval_proof = Self::eval_bounded_prove(
            &c_prime,
            pp,
            z,
            &y_prime_fe,
            d_prime,
            b_prime,
            &mut coef_vec_int_prime[..],
        );
        y_l_vec.extend_from_slice(&eval_proof.y_l_vec[..]);
        y_r_vec.extend_from_slice(&eval_proof.y_r_vec[..]);
        c_l_vec.extend_from_slice(&eval_proof.c_l_vec[..]);
        c_r_vec.extend_from_slice(&eval_proof.c_r_vec[..]);
        poe_proof_vec.extend_from_slice(&eval_proof.poe_proof_vec[..]);

        NiEvalProof {
            y_l_vec,
            y_r_vec,
            c_l_vec,
            c_r_vec,
            poe_proof_vec,
            f_const: eval_proof.f_const.clone(),
            d,
            b,
        }
    }
}

impl NiEvalProof {
    pub fn eval_verify(
        mut self,
        c: BinaryQF,
        pp: &PP,
        z: &Scalar<Secp256k1>,
        y: &Scalar<Secp256k1>,
    ) -> Result<(), ErrorReason> {
        unsafe { pari_init(100000000000, 2) };

        let mut flag = true;
        if self.d == 0 {
            //step3
            let bound: u32 = 2 * (BigInt::from(self.d as i32) + BigInt::one()).bit_length() as u32;

            let sig_p_d = pp.p.pow(bound);

            if sig_p_d * &self.b > pp.q {
                flag = false;
            }
            //step 4:
            if self.f_const.abs() > self.b {
                flag = false;
            }
            // step 5:

            if y != &Scalar::<Secp256k1>::from(&self.f_const.mod_floor(&pp.p)) {
                flag = false;
            }

            // step 6
            if pp.g.exp(&self.f_const).reduce() != c {
                flag = false;
            }

            match flag {
                true => return Ok(()),
                false => return Err(ErrorReason::EvalError),
            }
        }

        if (self.d + 1) % 2 == 1 {
            let d_prime = self.d + 1;
            let c_prime = c.exp(&pp.q);
            let y_prime = y * z;
            let b_prime = &self.b * BigInt::from(self.d as u32);

            self.b = b_prime;
            self.d = d_prime;

            let result = self.eval_verify(c_prime, pp, z, &y_prime);
            match result {
                Ok(()) => return Ok(()),
                Err(_) => return Err(ErrorReason::EvalError),
            }
        }
        //step 12
        let d_prime = (self.d + 1) / 2 - 1;
        // pop out y_l, y_r.
        let y_l = self.y_l_vec.remove(0);
        let y_r = self.y_r_vec.remove(0);

        //step 17
        let z_pow_d_prime_p1 =
            BigInt::mod_pow(&z.to_bigint(), &BigInt::from((d_prime + 1) as u32), &pp.p);
        let y_r_z_pow_d_prime_p1 = BigInt::mod_mul(&z_pow_d_prime_p1, &y_r, &pp.p);
        let y_l_y_r_z_pow_d_prime_p1 = BigInt::mod_add(&y_r_z_pow_d_prime_p1, &y_l, &pp.p);
        if y.to_bigint() != y_l_y_r_z_pow_d_prime_p1 {
            flag = false;
        }

        // step 18
        let poe_proof = self.poe_proof_vec.remove(0);
        let c_l = self.c_l_vec.remove(0);
        let c_r = self.c_r_vec.remove(0);
        let q_pow_d_prime_plus1 = pp.q.pow((d_prime + 1) as u32);

        let c_l_inverse = c_l.inverse();
        let c_over_c_l = c_l_inverse.compose(&c).reduce();

        let result = poe_proof.verify();

        if result.is_err()
            || c_over_c_l != poe_proof.w
            || c_r != poe_proof.u
            || q_pow_d_prime_plus1 != poe_proof.x
        {
            flag = false;
        }

        //step 19
        // alpha = H(y_l ||y_r) for Fiat-Shamir
        let alpha = Sha256::new()
            .chain_bigint(&y_l)
            .chain_bigint(&y_r)
            .result_bigint();
        let mut alpha = alpha.mod_floor(&pp.p);
        if alpha > (&pp.p - BigInt::one()).div_floor(&BigInt::from(2)) {
            alpha -= &pp.p;
        }

        //step 20
        let y_prime: BigInt = &alpha * &y_l + &y_r;
        let y_prime_fe = Scalar::<Secp256k1>::from(&y_prime);
        let c_prime = c_l.exp(&alpha).compose(&c_r).reduce();
        let b_prime = &self.b * ((&pp.p + BigInt::one()).div_floor(&BigInt::from(2)));

        self.b = b_prime;
        self.d = d_prime;
        let res = self.eval_verify(c_prime, pp, z, &y_prime_fe);
        if flag && res.is_ok() {
            Ok(())
        } else {
            Err(ErrorReason::EvalError)
        }
    }
}

// helper function: generate random group element from disc (used in setup)
// see protocol description in vdf h_g function
fn pick_random_element(disc: &BigInt) -> BinaryQF {
    let two = BigInt::from(2);
    let max = BigInt::from(20);
    let mut b = &two * BigInt::sample(disc.bit_length()) + BigInt::one();
    let mut c = two.clone();
    let mut b2_minus_disc: BigInt = b.pow(2) - disc;
    let four = BigInt::from(4);
    let mut u = b2_minus_disc.div_floor(&four);
    while u.mod_floor(&c) != BigInt::zero() {
        b = &two * BigInt::sample(disc.bit_length()) + BigInt::one();
        b2_minus_disc = b.pow(2) - disc;
        u = b2_minus_disc.div_floor(&four);
        c = (&c.next_prime()).mod_floor(&max);
    }
    let a = u.div_floor(&c);
    let a_b_delta = ABDeltaTriple {
        a,
        b,
        delta: disc.clone(),
    };

    BinaryQF::binary_quadratic_form_disc(&a_b_delta).reduce()
}

#[cfg(test)]
mod tests {
    use super::PolyComm;
    use curv::arithmetic::traits::*;
    use curv::elliptic::curves::{secp256_k1::Secp256k1, Scalar};
    use curv::BigInt;

    #[test]
    fn test_commit_open() {
        // sample coef vector
        for _ in 1..2 {
            let mut coef_vec: Vec<Scalar<Secp256k1>> = Vec::new();
            let mut i = 0;
            while i < 10 {
                // TODO: check that i < d_max
                coef_vec.push(Scalar::<Secp256k1>::random());
                i += 1;
            }
            let d_max = BigInt::from(64);

            let pp = PolyComm::setup(&d_max);

            let (c, _f_q) = PolyComm::commit(&pp, &coef_vec);

            let res = c.open(&pp, &coef_vec);

            assert!(res.is_ok());
        }
    }

    #[test]
    fn test_encode_decode() {
        // sample coef vector
        let mut coef_vec: Vec<Scalar<Secp256k1>> = Vec::new();
        let mut i = 0;
        while i < 10 {
            // TODO: check that i < d_max
            coef_vec.push(Scalar::<Secp256k1>::random());
            i += 1;
        }
        let d_max = BigInt::from(11);
        let pp = PolyComm::setup(&d_max);
        let z = PolyComm::encode(&pp.p, &pp.q, &coef_vec[..]);

        let coef_vec_dec = PolyComm::decode(&pp.p, &pp.q, &z);

        assert_eq!(coef_vec_dec, coef_vec);
    }

    #[test]
    fn test_encode_decode_toy_example() {
        let p = BigInt::from(20); // apparently the p in the toy example from the paper is too small (problem with doing -p/2)
                                  // let q = BigInt::from(10);
        let d_max = 10;
        let bound = 3 * (BigInt::one() + d_max).bit_length() as u32 + 1;
        let q = p.pow(bound);

        let mut coef_vec: Vec<Scalar<Secp256k1>> = Vec::new();

        coef_vec.push(Scalar::<Secp256k1>::from(&BigInt::from(2)));
        coef_vec.push(Scalar::<Secp256k1>::from(&BigInt::from(3)));
        coef_vec.push(Scalar::<Secp256k1>::from(&BigInt::from(4)));
        coef_vec.push(Scalar::<Secp256k1>::from(&BigInt::from(1)));

        let z = PolyComm::encode(&p, &q, &coef_vec[..]);

        let coef_vec_dec = PolyComm::decode(&p, &q, &z);

        assert_eq!(coef_vec_dec, coef_vec);
    }

    #[test]
    fn test_eval() {
        // create commitment:
        // sample coef vector
        let mut coef_vec: Vec<Scalar<Secp256k1>> = Vec::new();
        let mut i = 0;
        while i < 8 {
            // TODO: check that i < d_max
            coef_vec.push(Scalar::<Secp256k1>::random());
            i += 1;
        }
        let d_max = BigInt::from(11);
        let pp = PolyComm::setup(&d_max);
        for _ in 0..6 {
            let (c, _f_q) = PolyComm::commit(&pp, &coef_vec);
            // generate y,z
            let z = Scalar::<Secp256k1>::random();

            let mut coef_vec_rev = coef_vec.iter().rev();
            let head = coef_vec_rev.next().unwrap();
            let tail = coef_vec_rev;

            let y: Scalar<Secp256k1> = tail.fold(head.clone(), |acc, x| x + &(acc * &z));
            //create proof:
            let proof = c.eval_prove(&pp, &z, &y, &coef_vec[..]);
            let result = proof.eval_verify(c.c, &pp, &z, &y);
            assert!(result.is_ok());
        }
    }

    #[test]
    #[should_panic]
    fn test_eval_wrong_eval() {
        // here y != f(z)
        // create commitment:
        // sample coef vector
        let mut coef_vec: Vec<Scalar<Secp256k1>> = Vec::new();
        let mut i = 0;
        while i < 9 {
            // TODO: check that i < d_max
            coef_vec.push(Scalar::<Secp256k1>::random());
            i += 1;
        }
        let d_max = BigInt::from(11);
        let pp = PolyComm::setup(&d_max);
        let (c, _f_q) = PolyComm::commit(&pp, &coef_vec);

        // generate y,z
        let z = Scalar::<Secp256k1>::random();

        let mut coef_vec_rev = coef_vec.iter().rev();
        let head = coef_vec_rev.next().unwrap();
        let tail = coef_vec_rev;

        let y = tail.fold(head.clone(), |acc, x| x + &(acc * &z));
        let bias = Scalar::<Secp256k1>::from(&BigInt::from(2));
        let y = y + bias;
        //create proof:
        let proof = c.eval_prove(&pp, &z, &y, &coef_vec[..]);
        let result = proof.eval_verify(c.c, &pp, &z, &y);
        assert!(result.is_ok());
    }
}
