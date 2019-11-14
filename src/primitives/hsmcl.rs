use crate::curv::arithmetic::traits::Modulo;
use crate::curv::cryptographic_primitives::hashing::traits::Hash;
use crate::pari_init;
use crate::rayon::prelude::*;
use crate::BinaryQF;
use curv::arithmetic::traits::Samplable;
use curv::cryptographic_primitives::hashing::hash_sha256::HSha256;
use curv::elliptic::curves::traits::{ECPoint, ECScalar};
use curv::BigInt;
use curv::{FE, GE};
use paillier::keygen;
const SECURITY_PARAMETER: usize = 128;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PK {
    pub q: BigInt,
    pub delta_k: BigInt,
    pub delta_q: BigInt,
    pub gq: BinaryQF,
    pub h: BinaryQF,
    pub stilde: BigInt,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Ciphertext {
    pub c1: BinaryQF,
    pub c2: BinaryQF,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct HSMCL {
    pub sk: BigInt,
    pub pk: PK,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CLDLProof {
    pub pk: PK,
    pub ciphertext: Ciphertext,
    q: GE,
    t_vec: Vec<TTriplets>,
    u_vec: Vec<U1U2>,
}

pub struct Witness {
    pub r: BigInt,
    pub x: BigInt,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TTriplets {
    pub t1: BinaryQF,
    pub t2: GE,
    pub t3: BinaryQF,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct U1U2 {
    pub u1: BigInt,
    pub u2: BigInt,
}

#[derive(Debug)]
pub struct ProofError;

// based on https://eprint.iacr.org/2019/503.pdf figures 6 and 7
impl HSMCL {
    pub fn keygen(q: &BigInt, lam: &usize) -> Self {
        unsafe { pari_init(10000000, 2) };
        let mu = q.bit_length();
        assert!(lam > &(mu + 2));
        let k = lam - mu;
        let two = BigInt::from(2);
        let mut r = BigInt::sample_range(
            &two.pow((k - 1) as u32),
            &(two.pow(k as u32) - BigInt::one()),
        );

        let mut qtilde = next_probable_prime(&r);

        while (q * &qtilde).mod_floor(&BigInt::from(4)) != BigInt::from(3)
            || jacobi(q, &qtilde).unwrap() != -1
        {
            r = BigInt::sample_range(
                &two.pow((k - 1) as u32),
                &(two.pow(k as u32) - BigInt::one()),
            );
            qtilde = next_probable_prime(&r);
        }

        assert!(&(BigInt::from(4) * q) < &qtilde);

        let delta_k = -q * &qtilde;
        let delta_q = &delta_k * q.pow(2);

        let delta_k_abs: BigInt = -delta_k.clone();
        let log_delta_k_abs = numerical_log(&delta_k_abs);
        let delta_k_abs_sqrt = delta_k_abs.sqrt();
        let stilde = log_delta_k_abs * delta_k_abs_sqrt;

        let mut r = BigInt::from(3);
        while jacobi(&delta_k, &r).unwrap() != 1 {
            r = next_probable_prime(&r)
        }

        let rgoth = BinaryQF::primeform(&delta_k, &r);

        let (rgoth_square, _) = rgoth.compose(&rgoth).reduce();

        let (gq_tmp, _) = rgoth_square.phi_q_to_the_minus_1(&q).reduce();

        let gq = gq_tmp.exp(&q);

        let x = BigInt::sample_below(&(&stilde * BigInt::from(2).pow(40)));
        let h = gq.exp(&x);

        let pk = PK {
            q: q.clone(),
            delta_k,
            delta_q,
            gq,
            h,
            stilde,
        };
        HSMCL { sk: x, pk }
    }

    pub fn encrypt(pk: &PK, m: &BigInt) -> Ciphertext {
        unsafe { pari_init(10000000, 2) };
        assert!(m < &pk.q);
        let r = BigInt::sample_below(&(&pk.stilde * BigInt::from(2).pow(40)));
        let exp_f = BinaryQF::expo_f(&pk.q, &pk.delta_q, &m);
        let h_exp_r = pk.h.exp(&r);

        Ciphertext {
            c1: pk.gq.exp(&r),
            c2: h_exp_r.compose(&exp_f).reduce().0,
            // c2: s,
        }
    }

    pub fn encrypt_predefined_randomness(pk: &PK, m: &BigInt, r: &BigInt) -> Ciphertext {
        unsafe { pari_init(10000000, 2) };
        assert!(m < &pk.q);
        let exp_f = BinaryQF::expo_f(&pk.q, &pk.delta_q, &m);
        let h_exp_r = pk.h.exp(r);

        Ciphertext {
            c1: pk.gq.exp(r),
            c2: h_exp_r.compose(&exp_f).reduce().0,
            // c2: s,
        }
    }

    pub fn decrypt(&self, c: &Ciphertext) -> BigInt {
        unsafe { pari_init(10000000, 2) };
        let c1_x = c.c1.exp(&self.sk);
        let c1_x_inv = c1_x.inverse();
        let tmp = c.c2.compose(&c1_x_inv).reduce().0;
        BinaryQF::discrete_log_f(&self.pk.q, &self.pk.delta_q, &tmp)
    }

    //TODO: add unit test
    pub fn eval_scal(c: &Ciphertext, val: &BigInt) -> Ciphertext {
        unsafe { pari_init(10000000, 2) };
        let c_new = Ciphertext {
            c1: c.c1.exp(&val),
            c2: c.c2.exp(&val),
        };
        c_new
    }

    //TODO: add unit test
    pub fn eval_sum(c1: &Ciphertext, c2: &Ciphertext) -> Ciphertext {
        unsafe { pari_init(10000000, 2) };
        let c_new = Ciphertext {
            c1: c1.c1.compose(&c2.c1).reduce().0,
            c2: c1.c2.compose(&c2.c2).reduce().0,
        };
        c_new
    }
}

pub fn next_probable_prime(r: &BigInt) -> BigInt {
    let one = BigInt::from(1);
    let mut qtilde = r + &one;
    while !keygen::is_prime(&qtilde) {
        qtilde = qtilde + &one;
    }
    qtilde
}

// Automatically using q of the curve.
impl CLDLProof {
    pub fn prove(w: Witness, pk: PK, ciphertext: Ciphertext, q: GE) -> Self {
        unsafe { pari_init(10000000, 2) };

        let triplets_and_fs_and_r_vec = (0..SECURITY_PARAMETER)
            .map(|_| {
                let r1 = BigInt::sample_below(&(&pk.stilde * BigInt::from(2).pow(40)));
                let r2_fe: FE = FE::new_random();
                let r2 = r2_fe.to_big_int();
                let fr2 = BinaryQF::expo_f(&pk.q, &pk.delta_q, &r2);
                let pkr1 = pk.h.exp(&r1);
                let t1 = fr2.compose(&pkr1).reduce().0;
                let t2 = GE::generator() * r2_fe;
                let t3 = pk.gq.exp(&r1);
                let fs = HSha256::create_hash(&[
                    &BigInt::from(&t1.to_bytes()[..]),
                    &t2.bytes_compressed_to_big_int(),
                    &BigInt::from(&t3.to_bytes()[..]),
                ]);
                (TTriplets { t1, t2, t3 }, fs, r1, r2)
            })
            .collect::<Vec<(TTriplets, BigInt, BigInt, BigInt)>>();
        let triplets_vec = (0..SECURITY_PARAMETER)
            .map(|i| triplets_and_fs_and_r_vec[i].0.clone())
            .collect::<Vec<TTriplets>>();
        let fiat_shamir_vec = (0..SECURITY_PARAMETER)
            .map(|i| &triplets_and_fs_and_r_vec[i].1)
            .collect::<Vec<&BigInt>>();
        let r1_vec = (0..SECURITY_PARAMETER)
            .map(|i| triplets_and_fs_and_r_vec[i].2.clone())
            .collect::<Vec<BigInt>>();
        let r2_vec = (0..SECURITY_PARAMETER)
            .map(|i| triplets_and_fs_and_r_vec[i].3.clone())
            .collect::<Vec<BigInt>>();
        // using Fiat Shamir transform
        let k = HSha256::create_hash(&fiat_shamir_vec);

        let one = BigInt::one();
        let u1u2_vec = (0..SECURITY_PARAMETER)
            .map(|i| {
                let bit = (k.clone() >> i) & one.clone();

                let u1 = r1_vec[i].clone() + &bit * &w.r;
                let u2 = BigInt::mod_add(&r2_vec[i], &(&bit * &w.x), &FE::q());
                U1U2 { u1, u2 }
            })
            .collect::<Vec<U1U2>>();
        CLDLProof {
            pk,
            ciphertext,
            q,
            t_vec: triplets_vec,
            u_vec: u1u2_vec,
        }
    }

    pub fn verify(&self) -> Result<(), ProofError> {
        unsafe { pari_init(10000000, 2) };
        // reconstruct k
        let fs_vec = (0..SECURITY_PARAMETER)
            .map(|i| {
                HSha256::create_hash(&[
                    &BigInt::from(&self.t_vec[i].t1.to_bytes()[..]),
                    &self.t_vec[i].t2.bytes_compressed_to_big_int(),
                    &BigInt::from(&self.t_vec[i].t3.to_bytes()[..]),
                ])
            })
            .collect::<Vec<BigInt>>();
        let fs_t_vec = (0..SECURITY_PARAMETER)
            .map(|i| &fs_vec[i])
            .collect::<Vec<&BigInt>>();
        let mut flag = true;
        let k = HSha256::create_hash(&fs_t_vec[..]);
        let one = BigInt::one();

        for i in 0..SECURITY_PARAMETER {
            let bit = (k.clone() >> i) & one.clone();

            let t1 = self.t_vec[i].t1.clone();
            let c2k = self.ciphertext.c2.exp(&bit);
            let t1c2k = self.t_vec[i].t1.compose(&c2k).reduce().0;
            let pku1 = self.pk.h.exp(&self.u_vec[i].u1);
            let fu2 = BinaryQF::expo_f(&self.pk.q, &self.pk.delta_q, &self.u_vec[i].u2);
            let pku1fu2 = pku1.compose(&fu2).reduce().0;
            if t1c2k != pku1fu2 {
                flag = false;
            }
            //   let q = FE::q();
            //  let kq = bit + q;
            let bit_bias_fe: FE = ECScalar::from(&(bit.clone() + one.clone()));
            let g = GE::generator();
            let t2kq =
                (self.t_vec[i].t2 + self.q.clone() * bit_bias_fe).sub_point(&self.q.get_element());
            let u2p = &g * &ECScalar::from(&self.u_vec[i].u2);
            if t2kq != u2p {
                flag = false;
            }

            let c1k = self.ciphertext.c1.exp(&bit);
            let t3c1k = self.t_vec[i].t3.compose(&c1k).reduce().0;
            let gqu1 = self.pk.gq.exp(&&self.u_vec[i].u1);
            if t3c1k != gqu1 {
                flag = false
            };
        }
        match flag {
            true => Ok(()),
            false => Err(ProofError),
        }
    }
}

// copied from https://docs.rs/crate/quadratic/0.3.1/source/src/lib.rs
// changed to support BigInt
// TODO: put in utility module, expend to Kronecker
pub fn jacobi(a: &BigInt, n: &BigInt) -> Option<i8> {
    let zero = BigInt::zero();
    // jacobi symbol is only defined for odd positive moduli
    if n.mod_floor(&BigInt::from(2)) == zero || n <= &BigInt::zero() {
        return None;
    }

    // Raise a mod n, then start the unsigned algorithm
    let mut acc = 1;
    let mut num = a.mod_floor(&n);
    let mut den = n.clone();
    loop {
        // reduce numerator
        num = num.mod_floor(&den);
        if num == zero {
            return Some(0);
        }

        // extract factors of two from numerator
        while num.mod_floor(&BigInt::from(2)) == zero {
            acc *= two_over(&den);
            num = num.div_floor(&BigInt::from(2));
        }
        // if numerator is 1 => this sub-symbol is 1
        if num == BigInt::one() {
            return Some(acc);
        }
        // shared factors => one sub-symbol is zero
        if num.gcd(&den) > BigInt::one() {
            return Some(0);
        }
        // num and den are now odd co-prime, use reciprocity law:
        acc *= reciprocity(&num, &den);
        let tmp = num;
        num = den.clone();
        den = tmp;
    }
}

fn two_over(n: &BigInt) -> (i8) {
    if n.mod_floor(&BigInt::from(8)) == BigInt::one()
        || n.mod_floor(&BigInt::from(8)) == BigInt::from(7)
    {
        1
    } else {
        -1
    }
}

fn reciprocity(num: &BigInt, den: &BigInt) -> (i8) {
    if num.mod_floor(&BigInt::from(4)) == BigInt::from(3)
        && den.mod_floor(&BigInt::from(4)) == BigInt::from(3)
    {
        -1
    } else {
        1
    }
}

//TODO: improve approximation
fn numerical_log(x: &BigInt) -> BigInt {
    let mut ai: BigInt;
    let mut bi: BigInt;
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_encryption_p256() {
        let q = str::parse(
            "115792089210356248762697446949407573529996955224135760342422259061068512044369",
        )
        .unwrap();
        let hsmcl = HSMCL::keygen(&q, &516);
        let m = BigInt::from(1000);
        let ciphertext = HSMCL::encrypt(&hsmcl.pk, &m);
        let m_tag = hsmcl.decrypt(&ciphertext);

        assert_eq!(m, m_tag);
    }

    #[test]
    fn test_encryption_secp256k1() {
        // Taken from https://safecurves.cr.yp.to/base.html
        let q = str::parse(
            "115792089237316195423570985008687907852837564279074904382605163141518161494337",
        )
        .unwrap();
        let hsmcl = HSMCL::keygen(&q, &516);
        let m = BigInt::from(1000);
        let ciphertext = HSMCL::encrypt(&hsmcl.pk, &m);
        let m_tag = hsmcl.decrypt(&ciphertext);

        assert_eq!(m, m_tag);
    }

    #[test]
    fn test_zk_cl_dl() {
        // starts with hsm_cl encryption
        let q = str::parse(
            "115792089237316195423570985008687907852837564279074904382605163141518161494337",
        )
        .unwrap();
        let hsmcl = HSMCL::keygen(&q, &516);
        let m = BigInt::from(1000);
        let r = BigInt::sample_below(&(&hsmcl.pk.stilde * BigInt::from(2).pow(40)));
        let ciphertext = HSMCL::encrypt_predefined_randomness(&hsmcl.pk, &m, &r);
        let witness = Witness { x: m.clone(), r };
        let m_fe: FE = ECScalar::from(&m);
        let q = GE::generator() * m_fe;
        let proof = CLDLProof::prove(witness, hsmcl.pk.clone(), ciphertext, q);
        assert!(proof.verify().is_ok())
    }

    #[test]
    #[should_panic]
    fn test_bad_q_zk_cl_dl() {
        // starts with hsm_cl encryption
        let q = str::parse(
            "115792089237316195423570985008687907852837564279074904382605163141518161494337",
        )
        .unwrap();
        let hsmcl = HSMCL::keygen(&q, &516);
        let m = BigInt::from(1000);
        let r = BigInt::sample_below(&(&hsmcl.pk.stilde * BigInt::from(2).pow(40)));
        let ciphertext = HSMCL::encrypt_predefined_randomness(&hsmcl.pk, &m, &r);
        let witness = Witness { x: m.clone(), r };
        let m_fe: FE = ECScalar::from(&(&m + &BigInt::one()));
        let q = GE::generator() * m_fe;
        let proof = CLDLProof::prove(witness, hsmcl.pk.clone(), ciphertext, q);
        assert!(proof.verify().is_ok())
    }

    #[test]
    #[should_panic]
    fn test_bad_witness_zk_cl_dl() {
        // starts with hsm_cl encryption
        let q = str::parse(
            "115792089237316195423570985008687907852837564279074904382605163141518161494337",
        )
        .unwrap();
        let hsmcl = HSMCL::keygen(&q, &516);
        let m = BigInt::from(1000);
        let r = BigInt::sample_below(&(&hsmcl.pk.stilde * BigInt::from(2).pow(40)));
        let ciphertext = HSMCL::encrypt_predefined_randomness(&hsmcl.pk, &m, &r);
        let witness = Witness {
            x: m.clone() + BigInt::one(),
            r,
        };
        let m_fe: FE = ECScalar::from(&(&m + &BigInt::one()));
        let q = GE::generator() * m_fe;
        let proof = CLDLProof::prove(witness, hsmcl.pk.clone(), ciphertext, q);
        assert!(proof.verify().is_ok())
    }

    #[test]
    fn test_log_dlog() {
        let q = str::parse(
            "115792089210356248762697446949407573529996955224135760342422259061068512044369",
        )
        .unwrap();
        let hsmcl = HSMCL::keygen(&q, &516);
        let m = BigInt::from(10000);
        let exp_f = BinaryQF::expo_f(&hsmcl.pk.q, &hsmcl.pk.delta_q, &m);
        let m_tag = BinaryQF::discrete_log_f(&hsmcl.pk.q, &hsmcl.pk.delta_q, &exp_f);
        assert_eq!(m.clone(), m_tag);
    }

    #[test]
    fn test_log() {
        println!("TEST: {:?}", numerical_log(&BigInt::from(10)));
    }
}
