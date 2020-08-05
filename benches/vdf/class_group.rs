#[macro_use]
extern crate criterion;

use class_group::primitives::vdf::VDF;
use criterion::Criterion;
use curv::BigInt;

fn benches_class(c: &mut Criterion) {
    let bench_eval = |c: &mut Criterion, difficulty: &BigInt, disc: &BigInt, seed: &BigInt| {
        c.bench_function(&format!("eval with difficulty {}", difficulty), move |b| {
            b.iter(|| VDF::eval(&disc, &seed, &difficulty))
        });
    };
    let bench_verify =
        |c: &mut Criterion, difficulty: &BigInt, disc: &BigInt, vdf_out_proof: &VDF| {
            c.bench_function(
                &format!("verify with difficulty {}", difficulty),
                move |b| b.iter(|| vdf_out_proof.verify(&disc)),
            );
        };

    let sec = 1600;
    let disc = VDF::setup(sec);
    const TEST_HASH: &str = "1eeb30c7163271850b6d018e8282093ac6755a771da6267edf6c9b4fce9242ba";
    let seed = BigInt::from_str_radix(TEST_HASH, 16).unwrap();

    for &i in &[1_000, 2_000, 5_000, 10_000, 100_000, 1_000_000] {
        // precompute for verification
        let t = BigInt::from(i);
        let vdf_out_proof = VDF::eval(&disc, &seed, &t);
        let res = vdf_out_proof.verify(&disc);
        assert!(res.is_ok());

        bench_eval(c, &t, &disc, &seed);
        bench_verify(c, &t, &disc, &vdf_out_proof)
    }
}

criterion_group!(benches, benches_class);
criterion_main!(benches);
