use criterion::{black_box, criterion_group, criterion_main, Criterion};
use class_group::*;

/*
pub fn criterion_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("sampling Exp");
    // Configure Criterion.rs to detect smaller differences and increase sample size to improve
    // precision and counteract the resulting noise.
    group.significance_level(0.1).sample_size(20);
    group.bench_function("composing exp", |b| b.iter(|| bench_compose_exp()));
    group.finish();
}
*/

pub fn criterion_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("sampling Exp");
    group.significance_level(0.1).sample_size(10);
    for exp_size in (1000..7000).step_by(1000) {
        let dest = format!("exp 2048 bits by {:?} digits number",exp_size);
        group.bench_function(dest, |b| b.iter(|| bench_exp_only_for_a_given_det(black_box(exp_size))));
      //  group.bench_function(dest, |b| b.iter(|| bench_exp_only(black_box(exp_size))));

    }
    group.finish();

}


criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);