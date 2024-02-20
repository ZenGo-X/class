#[macro_use]
extern crate criterion;

use criterion::Criterion;
use rug::{integer::Order, Integer};
use sha2::{Digest, Sha256};

/// algo_2 from the paper
fn verify(modulus: &Integer, g: &Integer, t: u64, y: &Integer, pi: &Integer) -> bool {
    let l = &hash_to_prime(modulus, &[g, y]);

    let r = &Integer::from(2).pow_mod(&Integer::from(t), l).unwrap();
    let pi_l = pi.clone().pow_mod(l, modulus).unwrap();
    let g_r = g.clone().pow_mod(r, modulus).unwrap();
    let pi_l_g_r = pi_l * g_r;

    pi_l_g_r.div_rem_floor(modulus.clone()).1 == *y
}

/// algo_3 from the paper
fn eval(modulus: &Integer, g: &Integer, t: u64) -> (Integer, Integer) {
    // y <- (g^2)^t
    let mut y = g.clone();
    for _ in 0..t {
        y = y.clone() * y.clone();
        y = y.div_rem_floor(modulus.clone()).1;
    }

    let l = hash_to_prime(modulus, &[g, &y]);

    // algo_4 from the paper, long division
    // TODO: consider algo_5 instead
    let mut b: Integer;
    let mut r = Integer::from(1);
    let mut r2: Integer;
    let two = Integer::from(2);
    let mut pi = Integer::from(1);

    for _ in 0..t {
        r2 = r.clone() * two.clone();
        let quo_rem = r2.clone().div_rem_floor(l.clone());
        b = quo_rem.0;
        r = quo_rem.1;
        let pi_2 = pi.clone().pow_mod(&two, modulus).unwrap();
        let g_b = g.clone().pow_mod(&b, modulus).unwrap();
        pi = pi_2 * g_b;
    }

    (y, pi.div_rem_floor(modulus.clone()).1)
}

/// hashing an element onto the group
/// only run once, so won't downgrade the perfomance
fn h_g(modulus: &Integer, seed: &Integer) -> Integer {
    const HASH_ENT: u32 = 256;
    const GROUP_ENT: u32 = 2048;

    let prefix = "residue_part_".as_bytes();
    let seed_bytes = seed.to_digits::<u8>(Order::Lsf);

    // concat 8 sha256 to a 2048-bit hash
    let all_2048: Vec<u8> = (0..((GROUP_ENT / HASH_ENT) as u8))
        .map(|index| {
            let mut hasher = Sha256::new();
            hasher.update(prefix);
            hasher.update(vec![index]);
            hasher.update(seed_bytes.clone());
            hasher.finalize()
        })
        .flatten()
        .collect();
    let result = Integer::from_digits(&all_2048, Order::Lsf);
    result.div_rem_floor(modulus.clone()).1
}

fn hash_to_prime(modulus: &Integer, inputs: &[&Integer]) -> Integer {
    let mut hasher = Sha256::new();
    for input in inputs {
        hasher.update(input.to_digits::<u8>(Order::Lsf));
        hasher.update("\n".as_bytes());
    }
    let hashed = Integer::from_digits(&hasher.finalize(), Order::Lsf);
    hashed.next_prime().div_rem_floor(modulus.clone()).1
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

    /// RSA-2048 modulus, taken from [Wikipedia](https://en.wikipedia.org/wiki/RSA_numbers#RSA-2048).
    pub const MODULUS: &str =
    "251959084756578934940271832400483985714292821262040320277771378360436620207075955562640185258807\
    8440691829064124951508218929855914917618450280848912007284499268739280728777673597141834727026189\
    6375014971824691165077613379859095700097330459748808428401797429100642458691817195118746121515172\
    6546322822168699875491824224336372590851418654620435767984233871847744479207399342365848238242811\
    9816381501067481045166037730605620161967625613384414360383390441495263443219011465754445417842402\
    0924616515723350778707749817125772467962926386356373289912154831438167899885040445364023527381951\
    378636564391212010397122822120720357";
    let modulus = Integer::from_str_radix(MODULUS, 10).unwrap();

    const TEST_HASH: &str = "1eeb30c7163271850b6d018e8282093ac6755a771da6267edf6c9b4fce9242ba";
    let seed_hash = Integer::from_str_radix(TEST_HASH, 16).unwrap();
    let seed = seed_hash.div_rem_floor(modulus.clone()).1;

    // g <- H_G(x)
    let g = h_g(&modulus, &seed);

    for &i in &[1_000, 2_000, 5_000, 10_000, 100_000, 1_000_000] {
        // precompute for benchmarking verification
        let (y, pi) = eval(&modulus, &g, i);
        let result = verify(&modulus, &g, i, &y, &pi);
        assert!(result);

        bench_eval(c, i, &modulus, &seed);
        bench_verify(c, i, &modulus, &seed, &y, &pi)
    }
}

criterion_group!(benches, benches_rsa);
criterion_main!(benches);
