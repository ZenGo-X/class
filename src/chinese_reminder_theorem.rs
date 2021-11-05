// Taken from: https://gitlab.com/Toru3/ring-algorithm/-/blob/c4eaf606e88cb62cf87df98c99f923b253ad976a/src/lib.rs
// Original code is licensed under terms of: MIT OR Apache-2.0

use curv::arithmetic::*;

pub fn chinese_remainder_theorem(u: &[BigInt], m: &[BigInt]) -> Option<BigInt> {
    if u.len() != m.len() {
        return None;
    }
    let mut v = Vec::with_capacity(u.len());
    for (i, (u_i, m_i)) in u.iter().zip(m.iter()).enumerate() {
        let coef_i = BigInt::mod_inv(
            &m[0..i].iter().fold(BigInt::one(), |p, v| &(&p * v) % m_i),
            m_i,
        )?;
        let t = v
            .iter()
            .zip(m.iter())
            .rev()
            .fold(BigInt::zero(), |t, (v_j, m_j)| &(&(m_j * &t) + v_j) % m_i);
        v.push(&(&(u_i - &t) * &coef_i) % m_i);
    }
    let mut ret = v.pop().unwrap();
    for (v_i, m_i) in v.iter().zip(m.iter()).rev() {
        ret = &(&ret * m_i) + v_i;
    }
    Some(ret)
}
