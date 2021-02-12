use super::ErrorReason;
use crate::pari_init;
use crate::primitives::hash_to_prime;
use crate::BinaryQF;
use curv::arithmetic::traits::*;
use curv::BigInt;

/// This is a proof of exponentiation as given in https://eprint.iacr.org/2019/1229.pdf section 3.4
/// The prover can efficiently convince a verifier that a large exponentiation
/// in a group of unknown order was done correctly.
/// statement is (x,u,w), verifier accept if w = u^x.
///
#[derive(Clone, PartialEq, Eq, Debug, Serialize, Deserialize)]
pub struct PoEProof {
    pub x: BigInt,
    pub u: BinaryQF,
    pub w: BinaryQF,
    pub Q: BinaryQF,
}

impl PoEProof {
    // u^x = w
    pub fn prove(x: &BigInt, u: &BinaryQF, w: &BinaryQF) -> PoEProof {
        unsafe { pari_init(100000000000, 2) };
        let l = hash_to_prime(u, w);
        let r = x.mod_floor(&l);
        let q = (x - r).div_floor(&l);
        let Q = u.exp(&q);
        PoEProof {
            x: x.clone(),
            u: u.clone(),
            w: w.clone(),
            Q,
        }
    }

    pub fn verify(&self) -> Result<(), ErrorReason> {
        unsafe { pari_init(100000000000, 2) };
        let l = hash_to_prime(&self.u, &self.w);
        let r = self.x.mod_floor(&l);
        let Ql = self.Q.exp(&l);
        let ur = self.u.exp(&r);
        let left_side = Ql.compose(&ur).reduce();

        if left_side == self.w {
            Ok(())
        } else {
            Err(ErrorReason::PoEError)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::PoEProof;
    use crate::curv::arithmetic::traits::*;
    use crate::primitives::cl_dl_lcm::HSMCL;
    use curv::BigInt;

    #[test]
    fn test_poe_valid_proof() {
        for _ in 1..10 {
            let q = BigInt::from_str_radix(
                "115792089210356248762697446949407573529996955224135760342422259061068512044369",
                10,
            )
            .unwrap();
            let hsmcl = HSMCL::keygen(&q, &1600);
            let u = hsmcl.pk.gq;
            let x = BigInt::sample(512);
            let w = u.exp(&x);

            let proof = PoEProof::prove(&x, &u, &w);
            assert!(proof.verify().is_ok());
        }
    }

    #[test]
    #[should_panic]
    fn test_poe_invalid_proof() {
        let q = BigInt::from_str_radix(
            "115792089210356248762697446949407573529996955224135760342422259061068512044369",
            10,
        )
        .unwrap();
        let hsmcl = HSMCL::keygen(&q, &1600);
        let u = hsmcl.pk.gq;
        let x = BigInt::sample(512);
        let x_tag = &x + BigInt::from(1);
        let w = u.exp(&x_tag);
        let proof = PoEProof::prove(&x, &u, &w);
        assert!(proof.verify().is_ok());
    }
}
