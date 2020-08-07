#[macro_use]
extern crate criterion;

use criterion::Criterion;
use rug::Integer;
use sha2::{Digest, Sha256};

/// algo_2 from the paper
fn verify(modulus: &Integer, seed: &Integer, t: u64, y: &Integer, pi: &Integer) -> bool {
    let modulus = modulus.clone();

    // g <- H_G(x)
    let g = h_g(&modulus, &seed);

    let l = hash_to_prime(&modulus, &[&g, &y]);

    let r = Integer::from(2).pow_mod(&Integer::from(t), &l).unwrap();
    let pi_l = pi.clone().pow_mod(&l, &modulus).unwrap();
    let g_r = g.clone().pow_mod(&r, &modulus).unwrap();
    let pi_l_g_r = pi_l * g_r;

    Integer::from(pi_l_g_r.div_rem_floor(modulus.clone()).1) == y.clone()
}

/// algo_3 from the paper
fn eval(modulus: &Integer, seed: &Integer, t: u64) -> (Integer, Integer) {
    let modulus = modulus.clone();

    // g <- H_G(x)
    let g = h_g(&modulus, &seed);

    // y <- (g^2)^t
    let mut y = g.clone();
    for _ in 0..t {
        y = y.clone() * y.clone();
        y = y.div_rem_floor(modulus.clone()).1;
    }

    let l = hash_to_prime(&modulus, &[&g, &y]);

    // algo_4 from the paper, long division
    // TODO: consider algo_5 instead
    let mut b: Integer;
    let mut r = Integer::from(1);
    let mut r2: Integer;
    let two = Integer::from(2);
    let mut pi = Integer::from(1);

    for _ in 0..t {
        r2 = r.clone() * two.clone();
        b = r2.clone().div_rem_floor(l.clone()).0;
        r = r2.clone().div_rem_floor(l.clone()).1;
        let pi_2 = pi.clone().pow_mod(&Integer::from(2), &modulus).unwrap();
        let g_b = g.clone().pow_mod(&b, &modulus).unwrap();
        pi = pi_2 * g_b;
        pi = Integer::from(pi.div_rem_floor(modulus.clone()).1)
    }

    (y, pi)
}

/// int(H("residue"||x)) mod N
fn h_g(modulus: &Integer, seed: &Integer) -> Integer {
    let modulus = modulus.clone();
    let mut hasher = Sha256::new();
    hasher.update("residue".as_bytes());
    hasher.update(&seed.clone().to_string_radix(16).as_bytes());
    let result_hex = hasher.finalize();
    let result_hex_str = format!("{:#x}", result_hex);
    let result_int = Integer::from_str_radix(&result_hex_str, 16).unwrap();

    // invert to get enough security bits
    match result_int.invert(&modulus.clone()) {
        Ok(inverse) => inverse,
        Err(unchanged) => unchanged,
    }
}

fn hash_to_prime(modulus: &Integer, inputs: &[&Integer]) -> Integer {
    let mut hasher = Sha256::new();
    for input in inputs {
        hasher.update(input.to_string_radix(16).as_bytes());
        hasher.update("\n".as_bytes());
    }
    let hashed_hex = hasher.finalize();
    let hashed_hex_str = format!("{:#x}", hashed_hex);
    let hashed_int = Integer::from_str_radix(&hashed_hex_str, 16).unwrap();
    Integer::from(hashed_int.next_prime().div_rem_floor(modulus.clone()).1)
}

fn benches_rsa(c: &mut Criterion) {
    let bench_eval = |c: &mut Criterion, difficulty: u64, modulus: &Integer, seed: &Integer| {
        c.bench_function(&format!("eval with difficulty {}", difficulty), move |b| {
            b.iter(|| eval(&modulus, &seed, difficulty))
        });
    };
    let bench_verify = |c: &mut Criterion,
                        difficulty: u64,
                        modulus: &Integer,
                        seed: &Integer,
                        y: &Integer,
                        pi: &Integer| {
        c.bench_function(
            &format!("verify with difficulty {}", difficulty),
            move |b| b.iter(|| verify(&modulus, &seed, difficulty, &y, &pi)),
        );
    };

    // (M13 prime)
    const MODULUS: &str = "6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151"; // (M13 prime)
    let modulus = Integer::from_str_radix(MODULUS, 10).unwrap();

    const TEST_HASH: &str = "1eeb30c7163271850b6d018e8282093ac6755a771da6267edf6c9b4fce9242ba";
    let seed_hash = Integer::from_str_radix(TEST_HASH, 16).unwrap();
    let seed = Integer::from(seed_hash.div_rem_floor(modulus.clone()).1);

    for &i in &[1_000, 2_000, 5_000, 10_000, 100_000, 1_000_000] {
        // precompute for verification
        let (y, pi) = eval(&modulus, &seed, i);
        let result = verify(&modulus, &seed, i, &y, &pi);
        assert!(result);

        bench_eval(c, i, &modulus, &seed);
        bench_verify(c, i, &modulus, &seed, &y, &pi)
    }
}

criterion_group!(benches, benches_rsa);
criterion_main!(benches);
