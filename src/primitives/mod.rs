use super::{ABDeltaTriple, BinaryQF};
use crate::gmul;
use crate::pari_init;
use curv::arithmetic::traits::Samplable;
use curv::BigInt;
use paillier::keygen;
pub struct PK {
    pub q: BigInt,
    pub delta_k: BigInt,
    pub delta_q: BigInt,
    pub gq: BinaryQF,
    pub h: BinaryQF,
    stilde: BigInt,
}

pub struct Ciphertext {
    c1: BinaryQF,
    c2: BinaryQF,
}

pub struct HSMCL {
    sk: BigInt,
    pub pk: PK,
}

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

    pub fn decrypt(&self, c: &Ciphertext) -> BigInt {
        unsafe { pari_init(10000000, 2) };
        let c1_x = c.c1.exp(&self.sk);
        let c1_x_inv = c1_x.inverse();
        let tmp = c.c2.compose(&c1_x_inv).reduce().0;
        BinaryQF::discrete_log_f(&self.pk.q, &self.pk.delta_q, &tmp)
    }
}

pub fn next_probable_prime(r: &BigInt) -> BigInt {
    let mut qtilde = r + 1;
    while !keygen::is_prime(&qtilde) {
        qtilde = qtilde + 1;
    }
    qtilde
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
