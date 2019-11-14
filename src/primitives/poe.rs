use super::ProofError;
use crate::pari_init;
use crate::BinaryQF;
use curv::BigInt;
use paillier::keygen;

/// This is a proof of exponentiation as given in https://eprint.iacr.org/2019/1229.pdf section 3.4
/// The prover can efficiently convince a verifier that a large exponentiation
/// in a group of unknown order was done correctly.
/// statement is (x,u,w), verifier accept if w = u^x.
///
const SECURITY_PARAM: usize = 256;
#[derive(Clone, PartialEq, Debug, Serialize, Deserialize)]
pub struct PoEProof {
    pub x: BigInt,
    pub u: BinaryQF,
    pub w: BinaryQF,
    pub Q: BinaryQF,
    pub l: BigInt,
}

impl PoEProof {
    pub fn prove(x: &BigInt, u: &BinaryQF, w: &BinaryQF) -> PoEProof {
        unsafe {
            pari_init(10000000, 2);
        }
        let l = keygen::PrimeSampable::sample_prime(256);
        let r = x.mod_floor(&l);
        let q = (x - r).div_floor(&l);
        let Q = u.exp(&q);
        PoEProof {
            x: x.clone(),
            u: u.clone(),
            w: w.clone(),
            Q,
            l,
        }
    }

    pub fn verify(&self) -> Result<(), ProofError> {
        unsafe {
            pari_init(10000000, 2);
        }
        let r = self.x.mod_floor(&self.l);
        let Ql = self.Q.exp(&self.l);
        let ur = self.u.exp(&r);
        let left_side = Ql.compose(&ur).reduce().0;
        if left_side == self.w {
            Ok(())
        } else {
            Err(ProofError)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::PoEProof;
    use crate::curv::arithmetic::traits::Samplable;
    use crate::pari_init;
    use crate::primitives::hsmcl::HSMCL;
    use crate::ABDeltaTriple;
    use crate::BinaryQF;
    use curv::BigInt;

    #[test]
    fn test_poe_valid_proof() {
        unsafe {
            pari_init(10000000, 2);
        }
        let q = str::parse(
            "115792089210356248762697446949407573529996955224135760342422259061068512044369",
        )
        .unwrap();
        let hsmcl = HSMCL::keygen(&q, &516);
        let u = hsmcl.pk.gq;
        let x = BigInt::sample(512);
        let w = u.exp(&x);
        let proof = PoEProof::prove(&x, &u, &w);
        assert!(proof.verify().is_ok());
    }

    #[test]
    #[should_panic]
    fn test_poe_invalid_proof() {
        unsafe {
            pari_init(10000000, 2);
        }
        let q = str::parse(
            "115792089210356248762697446949407573529996955224135760342422259061068512044369",
        )
        .unwrap();
        let hsmcl = HSMCL::keygen(&q, &516);
        let u = hsmcl.pk.gq;
        let x = BigInt::sample(512);
        let x_tag = &x + BigInt::from(1);
        let w = u.exp(&x_tag);
        let proof = PoEProof::prove(&x, &u, &w);
        assert!(proof.verify().is_ok());
    }
}
