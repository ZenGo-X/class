#[macro_use]
extern crate criterion;

use class_group::primitives::vdf::VDF;
use class_group::ABDeltaTriple;
use criterion::Criterion;
use curv::{arithmetic::Converter, BigInt};

fn benches_class(c: &mut Criterion) {
    let bench_eval =
        |c: &mut Criterion, difficulty: &BigInt, a_b_delta: &ABDeltaTriple, seed: &BigInt| {
            c.bench_function(&format!("eval with difficulty {}", difficulty), move |b| {
                b.iter(|| VDF::eval(a_b_delta, seed, difficulty))
            });
        };
    let bench_verify = |c: &mut Criterion, difficulty: &BigInt, vdf_out_proof: &VDF| {
        c.bench_function(
            &format!("verify with difficulty {}", difficulty),
            move |b| b.iter(|| vdf_out_proof.verify()),
        );
    };

    let sec = 1600;
    const TEST_HASH: &str = "1eeb30c7163271850b6d018e8282093ac6755a771da6267edf6c9b4fce9242ba";
    let seed = BigInt::from_str_radix(TEST_HASH, 16).unwrap();
    let a_b_delta = VDF::setup(sec, &seed);

    // change below to `for &i in &[1_000, 2_000, 5_000, 10_000, 100_000, 1_000_000] {` if needed to expand test cases,
    // may also need to increase pari_init size (first parameter in `pari_init`) in src/primitives/vdf.rs
    for &i in &[1_0] {
        // precompute for verification
        let t = BigInt::from(i);
        let vdf_out_proof = VDF::eval(&a_b_delta, &seed, &t);
        let res = vdf_out_proof.verify();
        assert!(res.is_ok());

        bench_eval(c, &t, &a_b_delta, &seed);
        bench_verify(c, &t, &vdf_out_proof)
    }
}

criterion_group!(benches, benches_class);
criterion_main!(benches);
