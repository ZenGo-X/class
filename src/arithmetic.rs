//! Utilities for reusing ring algorithms from [ring-algorithm] crate

use std::ops;

use curv::arithmetic::big_gmp::BigInt;

/// Wrapper that implements arithmetic traits for [BigInt]
#[derive(Eq, PartialEq, Clone)]
pub struct A<T>(pub T);

impl<T> A<T> {
    pub fn into_inner(self) -> T {
        self.0
    }
}

impl<T> ops::Deref for A<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.0
    }
}

impl<T> ops::DerefMut for A<T> {
    fn deref_mut(&mut self) -> &mut T {
        &mut self.0
    }
}

macro_rules! impl_ops {
    ($($op: ident $func:ident ($($t:tt)+)),+$(,)?) => {
        $(
        impl ops::$op for &A<BigInt> {
            type Output = A<BigInt>;
            fn $func(self, rhs: Self) -> Self::Output {
                A(&self.0 $($t)+ &rhs.0)
            }
        }
        impl ops::$op for A<BigInt> {
            type Output = Self;
            fn $func(self, rhs: Self) -> Self::Output {
                &self $($t)+ &rhs
            }
        }
        )+
    };
}

impl_ops! {
    Add add (+),
    Sub sub (-),
    Mul mul (*),
    Div div (/),
    Rem rem (%),
}

impl num_traits::Zero for A<BigInt> {
    fn zero() -> Self {
        A(BigInt::zero())
    }

    fn is_zero(&self) -> bool {
        self.0 == BigInt::zero()
    }
}

impl num_traits::One for A<BigInt> {
    fn one() -> Self {
        A(BigInt::one())
    }
}

impl ring_algorithm::RingNormalize for A<BigInt> {
    fn leading_unit(&self) -> Self {
        if self.0 >= BigInt::zero() {
            A(BigInt::one())
        } else {
            A(-BigInt::one())
        }
    }

    fn normalize_mut(&mut self) {
        *self = A(self.abs())
    }
}

#[cfg(test)]
mod test {
    const PRIME: u32 = u32::MAX - 4;

    use super::*;
    use curv::arithmetic::traits::EGCD;

    proptest::proptest! {
        #[test]
        fn fuzz_inverse(n in 1..PRIME) {
            test_inverse(BigInt::from(n))
        }
        #[test]
        fn fuzz_xgcd(a in 1u32.., b in 1u32..) {
            test_xgcd(BigInt::from(a), BigInt::from(b))
        }
    }

    fn test_inverse(n: BigInt) {
        let prime = BigInt::from(PRIME);
        let n_inv_expected = n.invert(&prime).unwrap();
        let n_inv_actual = ring_algorithm::modulo_inverse(A(n), A(prime.clone())).unwrap();
        assert_eq!(n_inv_expected, n_inv_actual.into_inner().modulus(&prime));
    }

    fn test_xgcd(a: BigInt, b: BigInt) {
        let (s1, p1, q1) = BigInt::egcd(&a, &b);
        let (A(s2), A(p2), A(q2)) =
            ring_algorithm::normalized_extended_euclidian_algorithm(A(a), A(b));
        assert_eq!((s1, p1, q1), (s2, p2, q2));
    }
}
